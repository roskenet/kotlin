/*
 * Copyright 2000-2018 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.resolve.calls.inference.components

import org.jetbrains.kotlin.builtins.*
import org.jetbrains.kotlin.descriptors.annotations.Annotations
import org.jetbrains.kotlin.progress.ProgressIndicatorAndCompilationCanceledStatus
import org.jetbrains.kotlin.resolve.calls.NewCommonSuperTypeCalculator.commonSuperType
import org.jetbrains.kotlin.resolve.calls.components.transformToResolvedLambda
import org.jetbrains.kotlin.resolve.calls.inference.ConstraintSystemBuilder
import org.jetbrains.kotlin.resolve.calls.inference.NewConstraintSystem
import org.jetbrains.kotlin.resolve.calls.inference.model.*
import org.jetbrains.kotlin.resolve.calls.model.*
import org.jetbrains.kotlin.types.*
import org.jetbrains.kotlin.types.checker.intersectTypes
import org.jetbrains.kotlin.types.checker.intersectWrappedTypes
import org.jetbrains.kotlin.types.model.KotlinTypeMarker
import org.jetbrains.kotlin.types.model.TypeConstructorMarker
import org.jetbrains.kotlin.types.model.TypeVariableMarker
import org.jetbrains.kotlin.types.typeUtil.asTypeProjection
import org.jetbrains.kotlin.types.typeUtil.builtIns
import org.jetbrains.kotlin.types.typeUtil.contains
import org.jetbrains.kotlin.utils.addIfNotNull
import org.jetbrains.kotlin.utils.addToStdlib.safeAs
import kotlin.collections.LinkedHashSet

class KotlinConstraintSystemCompleter(
    private val resultTypeResolver: ResultTypeResolver,
    val variableFixationFinder: VariableFixationFinder,
) {
    enum class ConstraintSystemCompletionMode {
        FULL,
        PARTIAL
    }

    interface Context : VariableFixationFinder.Context, ResultTypeResolver.Context {
        override val notFixedTypeVariables: Map<TypeConstructorMarker, VariableWithConstraints>

        override val postponedTypeVariables: List<TypeVariableMarker>

        // type can be proper if it not contains not fixed type variables
        fun canBeProper(type: KotlinTypeMarker): Boolean

        fun containsOnlyFixedOrPostponedVariables(type: KotlinTypeMarker): Boolean

        // mutable operations
        fun addError(error: KotlinCallDiagnostic)

        fun fixVariable(variable: TypeVariableMarker, resultType: KotlinTypeMarker, atom: ResolvedAtom?)
    }

    fun runCompletion(
        c: Context,
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        topLevelType: UnwrappedType,
        diagnosticsHolder: KotlinDiagnosticsHolder,
        analyze: (PostponedResolvedAtom) -> Unit
    ) {
        c.runCompletion(
            completionMode,
            topLevelAtoms,
            topLevelType,
            diagnosticsHolder,
            collectVariablesFromContext = false,
            analyze = analyze
        )
    }

    fun completeConstraintSystem(
        c: Context,
        topLevelType: UnwrappedType,
        topLevelAtoms: List<ResolvedAtom>,
        diagnosticsHolder: KotlinDiagnosticsHolder
    ) {
        c.runCompletion(
            ConstraintSystemCompletionMode.FULL,
            topLevelAtoms,
            topLevelType,
            diagnosticsHolder,
            collectVariablesFromContext = true,
        ) {
            error("Shouldn't be called in complete constraint system mode")
        }
    }

    private fun Context.fixVariablesInsideConstraints(
        typeVariable: TypeVariableTypeConstructor,
        topLevelAtoms: List<ResolvedAtom>,
        completionMode: ConstraintSystemCompletionMode,
        topLevelType: UnwrappedType,
        typeVariablesSeen: MutableSet<TypeVariableTypeConstructor>
    ): Boolean? {
        if (typeVariablesSeen.contains(typeVariable)) return null

        typeVariablesSeen.add(typeVariable)

        val notFixedTypeVariable = notFixedTypeVariables[typeVariable] ?: return null
        if (notFixedTypeVariable.constraints.size == 0) return null

        return notFixedTypeVariable.constraints.toMutableList().map { constraint ->
            when {
                constraint.type.argumentsCount() > 0 -> {
                    val tt = if ((constraint.type as KotlinType).isBuiltinFunctionalType) {
                        constraint.type.arguments.map { it.type } // dropLast(1).
                    } else {
                        constraint.type.arguments.map { it.type }
                    }
                    fixVariablesInsideTypes(
                        tt,
                        topLevelAtoms,
                        completionMode,
                        topLevelType,
                        typeVariablesSeen
                    )
                }
                constraint.type.lowerBoundIfFlexible().typeConstructor() is TypeVariableTypeConstructor -> {
                    fixVariablesInsideTypes(listOf(constraint.type as KotlinType), topLevelAtoms, completionMode, topLevelType, typeVariablesSeen)
                }
                else -> false
            }
        }.all { it }
    }

    private fun Context.fixVariablesInsideTypes(
        types: List<KotlinType>,
        topLevelAtoms: List<ResolvedAtom>,
        completionMode: ConstraintSystemCompletionMode,
        topLevelType: UnwrappedType,
        typeVariablesSeen: MutableSet<TypeVariableTypeConstructor> = mutableSetOf()
    ): Boolean {
        return types.map { type ->
            val typeConstructor = type.constructor
            if (typeConstructor is TypeVariableTypeConstructor && notFixedTypeVariables.containsKey(typeConstructor)) {
                val isFixed = fixVariablesInsideConstraints(typeConstructor, topLevelAtoms, completionMode, topLevelType, typeVariablesSeen)

                val hasProperConstraint = variableFixationFinder.findFirstVariableForFixation(
                    this, listOf(typeConstructor), getOrderedNotAnalyzedPostponedArguments(topLevelAtoms), completionMode, topLevelType
                )?.hasProperConstraint == true

                if (hasProperConstraint) {
                    fixVariable(this, notFixedTypeVariables.getValue(typeConstructor), topLevelAtoms)
                    isFixed != null
                } else {
                    false
                }
            } else if (type.arguments.isNotEmpty()) {
                val tt = if (type.isBuiltinFunctionalType) {
                    type.arguments.map { it.type } //
                } else {
                    type.arguments.map { it.type }
                }

                fixVariablesInsideTypes(tt, topLevelAtoms, completionMode, topLevelType, typeVariablesSeen)
            } else {
                false
            }
        }.all { it } && types.size != 0
    }

    private fun Context.fixVariablesInsideArgument(
        argument: PostponedResolvedAtom,
        topLevelAtoms: List<ResolvedAtom>,
        completionMode: ConstraintSystemCompletionMode,
        topLevelType: UnwrappedType
    ): Boolean {
        val expectedType = argument.expectedType ?: return false
        val isExpectedTypeFunctionTypeWithArguments = expectedType.isBuiltinFunctionalType && expectedType.arguments.size > 1

        return if (isExpectedTypeFunctionTypeWithArguments) {
            fixVariablesInsideTypes(expectedType.arguments.dropLast(1).map { it.type }, topLevelAtoms, completionMode, topLevelType)
        } else if (expectedType.isBuiltinFunctionalType) {
            false
        } else {
            fixVariablesInsideTypes(listOf(expectedType), topLevelAtoms, completionMode, topLevelType)
        }
    }

    private fun Context.fixVariablesInsideFunctionTypeArguments(
        postponedArguments: List<PostponedResolvedAtom>,
        topLevelAtoms: List<ResolvedAtom>,
        completionMode: ConstraintSystemCompletionMode,
        topLevelType: UnwrappedType
    ) = postponedArguments.map { argument -> fixVariablesInsideArgument(argument, topLevelAtoms, completionMode, topLevelType) }
        .all { it } && postponedArguments.size != 0

    private fun Context.collectLambdaParameterTypes(argument: LambdaWithTypeVariableAsExpectedTypeAtom) {
        this as NewConstraintSystem

        fun <T : NewTypeVariable> createTypeVariableForLambda(
            typeVariableName: String,
            creator: Function3<LambdaKotlinCallArgument, KotlinBuiltIns, String, T>,
            record: LambdaWithTypeVariableAsExpectedTypeAtom.(T) -> Unit
        ) = creator(argument.atom, argument.expectedType.builtIns, typeVariableName).run {
            getBuilder().registerVariable(this)
            argument.record(this)
            defaultType
        }

        val parametersTypes = argument.atom.parametersTypes ?: return
        val parameters = parametersTypes.map { parametersType ->
            parametersType ?: createTypeVariableForLambda("_P", ::TypeVariableForLambdaInputType) {
                preparedParameterTypes.add(it)
            }
        }

        val preparedReturnType = createTypeVariableForLambda("_R", ::TypeVariableForLambdaReturnType) {
            preparedReturnType = it
        }

        val functionType = createFunctionType(
            argument.expectedType.builtIns, Annotations.EMPTY, null, parameters, null, preparedReturnType
        )

        getBuilder().addSubtypeConstraint(
            functionType, argument.expectedType, ArgumentConstraintPosition(argument.atom as KotlinCallArgument)
        )
    }

    private fun Context.runCompletion(
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        topLevelType: UnwrappedType,
        diagnosticsHolder: KotlinDiagnosticsHolder,
        collectVariablesFromContext: Boolean,
        analyze: (PostponedResolvedAtom) -> Unit
    ) {
        /*
         * Step 1: collect of parameter types of analyzing lambdas and add of corresponding constraints
         *      Example 1:
         *          Code: `select({ i: Int -> i.inv() }, ...)`
         *          Expected type: TypeVariable(K)
         *          Adding constraint: Function1<Int, TypeVariable(_R)> <: TypeVariable(K)
         *      Example 2:
         *          Code: `select({ i -> i.inv() }, ...)`
         *          Expected type: TypeVariable(K))
         *          Adding constraint: Function1<TypeVariable(_P), TypeVariable(_R)> <: TypeVariable(K)
         */
        if (completionMode == ConstraintSystemCompletionMode.PARTIAL) {
            val postponedArguments =
                getOrderedNotAnalyzedPostponedArguments(topLevelAtoms).filterIsInstance<LambdaWithTypeVariableAsExpectedTypeAtom>()
            for (argument in postponedArguments) {
                collectLambdaParameterTypes(argument)
            }
        }

        /*
         * Step 2: analyze postponed arguments with a type variable as an expected type and fix variables inside a function type
         */
        analyzePostponedArgumentsWithTypeVariableAsExpectedType(completionMode, topLevelAtoms, topLevelType, diagnosticsHolder, analyze)

        /*
         * Step 3: analyze remaining postponed arguments
         */
        analyzePostponedArguments(completionMode, topLevelAtoms, topLevelType, analyze)

        fixReadyVariablesOrReportNotEnoughInformation(completionMode, topLevelAtoms, topLevelType, collectVariablesFromContext)

        if (completionMode == ConstraintSystemCompletionMode.FULL) {
            forceAnalysisPostponedArguments(completionMode, topLevelAtoms, topLevelType, diagnosticsHolder, analyze)
        }
    }

    private fun Context.forceAnalysisPostponedArguments(
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        topLevelType: UnwrappedType,
        diagnosticsHolder: KotlinDiagnosticsHolder,
        analyze: (PostponedResolvedAtom) -> Unit
    ) {
        getOrderedNotAnalyzedPostponedArguments(topLevelAtoms).forEach(analyze)

        if (notFixedTypeVariables.isNotEmpty() && postponedTypeVariables.isEmpty()) {
            runCompletion(this, completionMode, topLevelAtoms, topLevelType, diagnosticsHolder, analyze)
        }
    }

    private fun Context.fixReadyVariablesOrReportNotEnoughInformation(
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        topLevelType: UnwrappedType,
        collectVariablesFromContext: Boolean
    ) {
        while (true) {
            val allTypeVariables = getOrderedAllTypeVariables(collectVariablesFromContext, topLevelAtoms)
            val postponedKtPrimitives = getOrderedNotAnalyzedPostponedArguments(topLevelAtoms)
            val variableForFixation = variableFixationFinder.findFirstVariableForFixation(
                this, allTypeVariables, postponedKtPrimitives, completionMode, topLevelType
            ) ?: break

            if (variableForFixation.hasProperConstraint || completionMode == ConstraintSystemCompletionMode.FULL) {
                val variableWithConstraints = notFixedTypeVariables.getValue(variableForFixation.variable)

                if (variableForFixation.hasProperConstraint)
                    fixVariable(this, variableWithConstraints, topLevelAtoms)
                else
                    processVariableWhenNotEnoughInformation(this, variableWithConstraints, topLevelAtoms)

                continue
            }

            break
        }
    }

    private fun Context.analyzePostponedArguments(
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        topLevelType: UnwrappedType,
        analyze: (PostponedResolvedAtom) -> Unit
    ) {
        fun analyzePostponeArgumentIfPossible(postponedArguments: List<PostponedResolvedAtom>, analyze: (PostponedResolvedAtom) -> Unit) =
            postponedArguments.any { argument ->
                ProgressIndicatorAndCompilationCanceledStatus.checkCanceled()
                if (canWeAnalyzeIt(argument)) {
                    analyze(argument)
                    true
                } else false
            }

        do {
            /*
             * We should compute not analyzed postponed arguments on each iteration
             * because analyze the first postponed argument can make possible analysis the second one (and it will appear in postponed argument list)
             */
            val postponedArguments = getOrderedNotAnalyzedPostponedArguments(topLevelAtoms)
            fixVariablesInsideFunctionTypeArguments(postponedArguments, topLevelAtoms, completionMode, topLevelType)
        } while (analyzePostponeArgumentIfPossible(postponedArguments, analyze))
    }

    private fun Context.analyzePostponedArgumentsWithTypeVariableAsExpectedType(
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        topLevelType: UnwrappedType,
        diagnosticsHolder: KotlinDiagnosticsHolder,
        analyze: (PostponedResolvedAtom) -> Unit
    ) {
        fun analyzePostponedArgumentWithTypeVariableAsExpectedTypeIfPossible(
            postponedArguments: List<PostponedResolvedAtom>,
            variableForFixation: VariableFixationFinder.VariableForFixation?
        ): Boolean {
            if (variableForFixation == null)
                return false

            val isAnalyzed =
                analyzePostponedArgumentWithTypeVariableAsExpectedType(variableForFixation, postponedArguments, diagnosticsHolder, analyze)

            fixVariablesInsideFunctionTypeArguments(postponedArguments, topLevelAtoms, completionMode, topLevelType)

            return isAnalyzed
        }

        do {
            /*
             * We should compute not analyzed postponed arguments on each iteration
             * because analyze the first postponed argument can make possible analysis the second one (and it will appear in postponed argument list)
             */
            val postponedArguments =
                getOrderedNotAnalyzedPostponedArguments(topLevelAtoms).filter { it.expectedType?.constructor is TypeVariableTypeConstructor }
            val expectedType = postponedArguments.firstOrNull()?.expectedType ?: break
            val variableForFixation = variableFixationFinder.findFirstVariableForFixation(
                this, listOf(expectedType.constructor), postponedArguments, completionMode, topLevelType
            )
        } while (analyzePostponedArgumentWithTypeVariableAsExpectedTypeIfPossible(postponedArguments, variableForFixation))
    }

    /*
     * returns true -> analyzed
     */
    private fun Context.analyzePostponedArgumentWithTypeVariableAsExpectedType(
        variableForFixation: VariableFixationFinder.VariableForFixation,
        postponedArguments: List<PostponedResolvedAtom>,
        diagnosticsHolder: KotlinDiagnosticsHolder,
        analyze: (PostponedResolvedAtom) -> Unit
    ): Boolean {
        if (this !is NewConstraintSystem) return false

        val variable = variableForFixation.variable as? TypeConstructor ?: return false
        val hasProperAtom = postponedArguments.any {
            when (it) {
                is LambdaWithTypeVariableAsExpectedTypeAtom, is PostponedCallableReferenceAtom ->
                    it.expectedType?.constructor == variable
                else -> false
            }
        }

        return postponedArguments.all { postponedAtom ->
            val expectedTypeAtom = postponedAtom.expectedType
            val expectedTypeVariable =
                expectedTypeAtom?.constructor?.takeIf { it in getBuilder().currentStorage().allTypeVariables } ?: variable

            val shouldAnalyzeByEqualityExpectedTypeToVariable =
                hasProperAtom || !variableForFixation.hasProperConstraint || variableForFixation.hasOnlyTrivialProperConstraint

            if (!shouldAnalyzeByEqualityExpectedTypeToVariable)
                return@all false

            analyze(
                preparePostponedAtom(expectedTypeVariable.typeForTypeVariable(), postponedAtom, variable.builtIns, diagnosticsHolder)
                    ?: return@all false
            )

            true
        }
    }

    private fun Context.preparePostponedAtom(
        expectedTypeVariable: UnwrappedType,
        postponedAtom: PostponedResolvedAtom,
        builtIns: KotlinBuiltIns,
        diagnosticsHolder: KotlinDiagnosticsHolder
    ): PostponedResolvedAtom? {
        val csBuilder = (this as? NewConstraintSystem)?.getBuilder() ?: return null

        return when (postponedAtom) {
            is PostponedCallableReferenceAtom -> postponedAtom.preparePostponedAtomWithTypeVariableAsExpectedType(
                this, csBuilder, expectedTypeVariable.constructor,
                parameterTypes = null,
                isSuitable = KotlinType::isBuiltinFunctionalTypeOrSubtype,
                typeVariableCreator = { TypeVariableForCallableReferenceReturnType(builtIns, "_Q") },
                newAtomCreator = { returnVariable, expectedType ->
                    CallableReferenceWithTypeVariableAsExpectedTypeAtom(postponedAtom.atom, expectedType, returnVariable).also {
                        postponedAtom.setAnalyzedResults(null, listOf(it))
                    }
                }
            )
            is LambdaWithTypeVariableAsExpectedTypeAtom -> postponedAtom.preparePostponedAtomWithTypeVariableAsExpectedType(
                this, csBuilder, expectedTypeVariable.constructor,
                parameterTypes = postponedAtom.atom.parametersTypes,
                isSuitable = KotlinType::isBuiltinFunctionalType,
                typeVariableCreator = {
                    postponedAtom.preparedReturnType ?: TypeVariableForLambdaReturnType(postponedAtom.atom, builtIns, "_R")
                },
                newAtomCreator = { returnVariable, expectedType ->
                    postponedAtom.transformToResolvedLambda(csBuilder, diagnosticsHolder, expectedType, returnVariable)
                }
            )
            else -> null
        }
    }

    fun Context.foundConstrainingType(type: KotlinType): KotlinType? {
        return if (type.constructor is TypeVariableTypeConstructor) {
            val v = notFixedTypeVariables.getValue(type.constructor)
            val resultType = resultTypeResolver.findResultTypeOrNull(this, v, TypeVariableDirectionCalculator.ResolveDirection.TO_SUBTYPE)

            if (resultType == null) {
                if (v.constraints.isNotEmpty()) {
                    intersectTypes(
                        v.constraints.mapNotNull {
                            foundConstrainingType(it.type as KotlinType)
                        }
                    ) as KotlinType
                } else null
            } else resultType as KotlinType
        } else {
            type
        }
    }

    fun Context.foundFunctionType(
        v: VariableWithConstraints,
        foundFunctionTypes: MutableSet<KotlinType>,
        typeVariablesSeen: MutableSet<TypeVariableTypeConstructor> = mutableSetOf()
    ) {
        if (typeVariablesSeen.contains(v.typeVariable.freshTypeConstructor() as TypeVariableTypeConstructor)) return
        typeVariablesSeen.add(v.typeVariable.freshTypeConstructor() as TypeVariableTypeConstructor)

        v.constraints.forEach {
            if ((it.type as KotlinType).isBuiltinFunctionalTypeOrSubtype) {
                foundFunctionTypes.add(
                    it.type.replace(
                        newArguments = it.type.arguments.dropLast(1).map {
                            foundConstrainingType(it.type)?.asTypeProjection() ?: it
                        } + (nullableAnyType() as KotlinType).asTypeProjection()
                    )
                )
            } else if (it.type.constructor in notFixedTypeVariables) {
                foundFunctionType(notFixedTypeVariables[it.type.constructor]!!, foundFunctionTypes, typeVariablesSeen)
            }
        }
    }

    fun <T : PostponedResolvedAtom, V : NewTypeVariable> T.preparePostponedAtomWithTypeVariableAsExpectedType(
        c: Context,
        csBuilder: ConstraintSystemBuilder,
        variable: TypeConstructor,
        parameterTypes: Array<out KotlinType?>?,
        isSuitable: KotlinType.() -> Boolean,
        typeVariableCreator: () -> V,
        newAtomCreator: (V, SimpleType) -> PostponedResolvedAtom
    ): PostponedResolvedAtom {
        if (variable !in c.notFixedTypeVariables) return this

        val functionalTypes = mutableSetOf<KotlinType>()
        val typeApproximator = TypeApproximator(variable.builtIns)

        c.foundFunctionType(c.notFixedTypeVariables.getValue(variable), functionalTypes)
        val functionalType = if (functionalTypes.isEmpty()) {
            resultTypeResolver.findResultType(
                c,
                c.notFixedTypeVariables.getValue(variable),
                TypeVariableDirectionCalculator.ResolveDirection.TO_SUPERTYPE
            ) as KotlinType
        } else {
            functionalTypes.first()
        }
        if (!functionalType.isSuitable()) return this

        val isExtensionFunction = functionalType.isExtensionFunctionType
        val isExtensionFunctionWithReceiverAsDeclaredParameter =
            isExtensionFunction && functionalType.arguments.size - 1 == parameterTypes?.filterNotNull()?.size
        if (parameterTypes?.all { type -> type != null } == true && (!isExtensionFunction || isExtensionFunctionWithReceiverAsDeclaredParameter)) return this

        val arguments = if (functionalTypes.isEmpty()) {
            functionalType.arguments.dropLast(1).toMutableList()
        } else {
            val arguments = mutableListOf<MutableList<UnwrappedType>>()

            for (f in functionalTypes) {
                for ((i, a) in f.arguments.dropLast(1).withIndex()) {
                    if (arguments.size <= i) {
                        arguments.add(mutableListOf())
                    }
                    arguments[i].add(a.type as UnwrappedType)
                }
            }


            val result = arguments.map {
                val properTypes = it.filter { it.constructor !is TypeVariableTypeConstructor }

                if (properTypes.isEmpty()) return this
                if (properTypes.size == 1) return@map properTypes.single().asTypeProjection()

                val interTypes = intersectTypes(properTypes)

                if (interTypes.contains { with (c) { (it.constructor as TypeConstructorMarker).isIntersection() } }) {
                    typeApproximator.approximateToSubType(
                        intersectTypes(properTypes),
                        TypeApproximatorConfiguration.PublicDeclaration
                    )?.asTypeProjection() ?: return this
                } else interTypes.asTypeProjection()
            }

            result
        }

        val returnVariable = typeVariableCreator()
        csBuilder.registerVariable(returnVariable)

        val expectedType =
            KotlinTypeFactory.simpleType(
                functionalType.annotations,
                functionalType.constructor,
                arguments + returnVariable.defaultType.asTypeProjection(),
                functionalType.isMarkedNullable
            )

        csBuilder.addSubtypeConstraint(
            expectedType,
            variable.typeForTypeVariable(),
            ArgumentConstraintPosition(atom as KotlinCallArgument)
        )
        return newAtomCreator(returnVariable, expectedType)
    }

    private fun Context.getOrderedAllTypeVariables(
        collectVariablesFromContext: Boolean,
        topLevelAtoms: List<ResolvedAtom>
    ): List<TypeConstructorMarker> {
        if (collectVariablesFromContext) return notFixedTypeVariables.keys.toList()

        fun ResolvedAtom.process(to: LinkedHashSet<TypeConstructor>) {
            val typeVariables = when (this) {
                is LambdaWithTypeVariableAsExpectedTypeAtom -> preparedParameterTypes + preparedReturnType
                is ResolvedCallAtom -> freshVariablesSubstitutor.freshVariables
                is CallableReferenceWithTypeVariableAsExpectedTypeAtom -> mutableListOf<NewTypeVariable>().apply {
                    addIfNotNull(typeVariableForReturnType)
                    addAll(candidate?.freshSubstitutor?.freshVariables.orEmpty())
                }
                is ResolvedCallableReferenceAtom -> candidate?.freshSubstitutor?.freshVariables.orEmpty()
                is ResolvedLambdaAtom -> listOfNotNull(typeVariableForLambdaReturnType)
                else -> emptyList()
            }

            typeVariables.filterNotNull().mapNotNullTo(to) {
                val typeConstructor = it.freshTypeConstructor
                typeConstructor.takeIf { notFixedTypeVariables.containsKey(typeConstructor) }
            }

            /*
             * Hack for completing error candidates in delegate resolve
             */
            if (this is StubResolvedAtom && typeVariable in notFixedTypeVariables) {
                to += typeVariable
            }

            if (analyzed) {
                subResolvedAtoms?.forEach { it.process(to) }
            }
        }

        // Note that it's important to use Set here, because several atoms can share the same type variable
        val result = linkedSetOf<TypeConstructor>()
        for (primitive in topLevelAtoms) {
            primitive.process(result)
        }

//        assert(result.size == c.notFixedTypeVariables.size) {
//            val notFoundTypeVariables = c.notFixedTypeVariables.keys.toMutableSet().apply { removeAll(result) }
//            "Not all type variables found: $notFoundTypeVariables"
//        }

        return result.toList()
    }


    private fun Context.canWeAnalyzeIt(argument: PostponedResolvedAtom): Boolean {
        if (argument.analyzed) return false

        return argument.inputTypes.all { containsOnlyFixedOrPostponedVariables(it) }
    }

    private fun fixVariable(
        c: Context,
        variableWithConstraints: VariableWithConstraints,
        topLevelAtoms: List<ResolvedAtom>
    ) {
        fixVariable(c, variableWithConstraints, TypeVariableDirectionCalculator.ResolveDirection.UNKNOWN, topLevelAtoms)
    }

    fun fixVariable(
        c: Context,
        variableWithConstraints: VariableWithConstraints,
        direction: TypeVariableDirectionCalculator.ResolveDirection,
        topLevelAtoms: List<ResolvedAtom>
    ) {
        val resultType = resultTypeResolver.findResultType(c, variableWithConstraints, direction)
        val resolvedAtom = findResolvedAtomBy(variableWithConstraints.typeVariable, topLevelAtoms) ?: topLevelAtoms.firstOrNull()
        c.fixVariable(variableWithConstraints.typeVariable, resultType, resolvedAtom)
    }

    private fun processVariableWhenNotEnoughInformation(
        c: Context,
        variableWithConstraints: VariableWithConstraints,
        topLevelAtoms: List<ResolvedAtom>
    ) {
        val typeVariable = variableWithConstraints.typeVariable

        val resolvedAtom = findResolvedAtomBy(typeVariable, topLevelAtoms) ?: topLevelAtoms.firstOrNull()
        if (resolvedAtom != null) {
            c.addError(NotEnoughInformationForTypeParameter(typeVariable, resolvedAtom))
        }

        val resultErrorType = if (typeVariable is TypeVariableFromCallableDescriptor)
            ErrorUtils.createUninferredParameterType(typeVariable.originalTypeParameter)
        else
            ErrorUtils.createErrorType("Cannot infer type variable $typeVariable")

        c.fixVariable(typeVariable, resultErrorType, resolvedAtom)
    }

    private fun findResolvedAtomBy(typeVariable: TypeVariableMarker, topLevelAtoms: List<ResolvedAtom>): ResolvedAtom? {
        fun ResolvedAtom.check(): ResolvedAtom? {
            val suitableCall = when (this) {
                is ResolvedCallAtom -> typeVariable in freshVariablesSubstitutor.freshVariables
                is ResolvedCallableReferenceAtom -> candidate?.freshSubstitutor?.freshVariables?.let { typeVariable in it } ?: false
                is ResolvedLambdaAtom -> typeVariable == typeVariableForLambdaReturnType
                else -> false
            }

            if (suitableCall) {
                return this
            }

            subResolvedAtoms?.forEach { subResolvedAtom ->
                subResolvedAtom.check()?.let { result -> return@check result }
            }

            return null
        }

        for (topLevelAtom in topLevelAtoms) {
            topLevelAtom.check()?.let { return it }
        }

        return null
    }

    companion object {
        fun getOrderedNotAnalyzedPostponedArguments(topLevelAtoms: List<ResolvedAtom>): List<PostponedResolvedAtom> {
            fun ResolvedAtom.process(to: MutableList<PostponedResolvedAtom>) {
                to.addIfNotNull(this.safeAs<PostponedResolvedAtom>()?.takeUnless { it.analyzed })

                if (analyzed) {
                    subResolvedAtoms?.forEach { it.process(to) }
                }
            }

            val notAnalyzedArguments = arrayListOf<PostponedResolvedAtom>()
            for (primitive in topLevelAtoms) {
                primitive.process(notAnalyzedArguments)
            }

            return notAnalyzedArguments
        }
    }
}