/*
 * Copyright 2000-2018 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.resolve.calls.inference.components

import org.jetbrains.kotlin.builtins.*
import org.jetbrains.kotlin.descriptors.annotations.Annotations
import org.jetbrains.kotlin.descriptors.annotations.BuiltInAnnotationDescriptor
import org.jetbrains.kotlin.descriptors.annotations.FilteredAnnotations
import org.jetbrains.kotlin.progress.ProgressIndicatorAndCompilationCanceledStatus
import org.jetbrains.kotlin.resolve.calls.components.transformToResolvedLambda
import org.jetbrains.kotlin.resolve.calls.inference.ConstraintSystemBuilder
import org.jetbrains.kotlin.resolve.calls.inference.NewConstraintSystem
import org.jetbrains.kotlin.resolve.calls.inference.model.*
import org.jetbrains.kotlin.resolve.calls.model.*
import org.jetbrains.kotlin.types.*
import org.jetbrains.kotlin.types.model.KotlinTypeMarker
import org.jetbrains.kotlin.types.model.TypeConstructorMarker
import org.jetbrains.kotlin.types.model.TypeVariableMarker
import org.jetbrains.kotlin.types.typeUtil.asTypeProjection
import org.jetbrains.kotlin.types.typeUtil.builtIns
import org.jetbrains.kotlin.utils.addIfNotNull
import org.jetbrains.kotlin.utils.addToStdlib.safeAs
import java.util.*
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

    fun <T : NewTypeVariable, K> NewConstraintSystem.createTypeVariableForLambda(
        argument: K,
        typeVariableName: String,
        creator: Function2<KotlinBuiltIns, String, T>,
        record: AtomWithTypeVariableAsExpectedType.(T) -> Unit
    ) where K : AtomWithTypeVariableAsExpectedType, K: PostponedResolvedAtom =
        creator(argument.expectedType!!.builtIns, typeVariableName).run {
            getBuilder().registerVariable(this)
            argument.record(this)
            defaultType
        }

    private fun extractParameterTypesFromDeclaration(atom: ResolutionAtom): Array<UnwrappedType?>? {
        return if (atom is FunctionExpression && atom.receiverType != null) {
            arrayOf(atom.receiverType) + atom.parametersTypes
        } else if (atom is LambdaKotlinCallArgument) atom.parametersTypes
        else null
    }

    data class Option(val baseType: KotlinType, val isSuspend: Boolean, val parameterTypes: List<List<UnwrappedType?>>?)

    private fun Context.extractParameterTypesFromConstraints(
        argument: PostponedResolvedAtom
    ): Option? {
        val expectedTypeVariable = argument.expectedType!!.constructor
        if (expectedTypeVariable !in notFixedTypeVariables) return null

        val foundFunctionalTypes = findFunctionalTypesInConstraints(notFixedTypeVariables.getValue(expectedTypeVariable))
        val baseFunctionalType = foundFunctionalTypes?.firstOrNull() ?: return null

        return Option(
            baseFunctionalType,
            foundFunctionalTypes.all { it.isSuspendFunctionTypeOrSubtype },
            foundFunctionalTypes.map {
                it.arguments.dropLast(1).map { it.type as UnwrappedType }
            }
        )
    }

    private fun <T> Context.fixParameterTypes(
        argument: T,
        diagnosticsHolder: KotlinDiagnosticsHolder
    ) where T : AtomWithTypeVariableAsExpectedType, T : PostponedResolvedAtom {
        if (argument.parameters3 != null) {
            argument.preparedParameterTypes.forEachIndexed { i, el ->
                if (argument.parameters3!![i].all { it != null }) {
                    fixVariable(this, notFixedTypeVariables.getValue(el.freshTypeConstructor), listOf(argument))
                }
            }

            val s = when (argument) {
                is PostponedCallableReferenceAtom -> {
                    CallableReferenceWithTypeVariableAsExpectedTypeAtom(
                        argument.atom,
                        argument.newExpectedType,
                        argument.returnValueVariable as TypeVariableForCallableReferenceReturnType
                    ).also {
                        argument.setAnalyzedResults(null, listOf(it))
                    }
                }
                is LambdaWithTypeVariableAsExpectedTypeAtom ->
                    argument.transformToResolvedLambda(
                        (this as NewConstraintSystem).getBuilder(),
                        diagnosticsHolder,
                        argument.newExpectedType,
                        argument.returnValueVariable as TypeVariableForLambdaReturnType
                    )
                else -> null!!
            }

            argument.expandedExpectedType = s
        }
    }

    private fun <T> Context.collectParameterTypes(argument: T) where T : AtomWithTypeVariableAsExpectedType, T : PostponedResolvedAtom {
        argument.areParameterTypesLooked2 = true
        if (argument.areParameterTypesLooked) return

        val atom = argument.atom ?: return
        val parametersFromDeclaration = extractParameterTypesFromDeclaration(atom)?.toList()
        val (baseFunctionalType, isSuspend, parametersFromConstraints) = extractParameterTypesFromConstraints(argument) ?: Option(
            argument.expectedType!!,
            false,
            null
        )

        val al = if (parametersFromDeclaration != null && parametersFromConstraints != null) {
            parametersFromConstraints + listOf(
                if (baseFunctionalType.arguments.size - 1 > parametersFromDeclaration.size) {
                    listOf(null) + parametersFromDeclaration
                } else {
                    parametersFromDeclaration
                }
            )
        } else if (parametersFromDeclaration != null) {
            listOf(parametersFromDeclaration)
        } else parametersFromConstraints ?: return

        argument.areParameterTypesLooked = true

        val allParameters = al.first().indices.map { i -> al.map { it[i] } }

        // -------

        val csBuilder = (this as NewConstraintSystem).getBuilder()
        val expectedTypeVariable = argument.expectedType!!

        val typeVariableCreatorForInputType = {
            when (argument) {
                is LambdaWithTypeVariableAsExpectedTypeAtom -> TypeVariableForLambdaInputType(expectedTypeVariable.builtIns, "_RP")
                is PostponedCallableReferenceAtom -> TypeVariableForCallableReferenceInputType(expectedTypeVariable.builtIns, "_QP")
                else -> null!!
            }
        }

        val typeVariableCreatorForReturnType = {
            when (argument) {
                is LambdaWithTypeVariableAsExpectedTypeAtom -> TypeVariableForLambdaReturnType(expectedTypeVariable.builtIns, "_R")
                is PostponedCallableReferenceAtom -> TypeVariableForCallableReferenceReturnType(expectedTypeVariable.builtIns, "_QP")
                else -> null!!
            }
        }
        val parameterVariables = allParameters.map { types ->
            val parameterTypeVariable = typeVariableCreatorForInputType().apply { csBuilder.registerVariable(this) }

            argument.preparedParameterTypes.add(parameterTypeVariable)

            types.forEach { type ->
                if (type != null) {
                    csBuilder.addSubtypeConstraint(
                        parameterTypeVariable.defaultType,
                        type,
                        ArgumentConstraintPosition(argument.atom as KotlinCallArgument)
                    )
                }
            }

            parameterTypeVariable.defaultType.asTypeProjection()
        }

        val returnValueVariable = typeVariableCreatorForReturnType().apply { csBuilder.registerVariable(this) }

        val newExpectedType =
            KotlinTypeFactory.simpleType(
                if (baseFunctionalType.isBuiltinExtensionFunctionalType && parametersFromDeclaration?.size == baseFunctionalType.arguments.size - 1 && parametersFromDeclaration.all { it != null } && baseFunctionalType.arguments.first().type == parametersFromDeclaration.first()) {
                    FilteredAnnotations(baseFunctionalType.annotations, true) { it != KotlinBuiltIns.FQ_NAMES.extensionFunctionType }
                } else if (argument.atom is FunctionExpression && (argument.atom as FunctionExpression).receiverType != null) {
                    Annotations.create(baseFunctionalType.annotations + BuiltInAnnotationDescriptor(baseFunctionalType.builtIns, KotlinBuiltIns.FQ_NAMES.extensionFunctionType, emptyMap()))
                } else baseFunctionalType.annotations,
                when (argument) {
                    is LambdaWithTypeVariableAsExpectedTypeAtom ->
                        if (isSuspend) baseFunctionalType.builtIns.getSuspendFunction(parameterVariables.size) else baseFunctionalType.builtIns.getFunction(
                            parameterVariables.size
                        )
                    is PostponedCallableReferenceAtom ->
                        if (isSuspend) baseFunctionalType.builtIns.getKSuspendFunction(parameterVariables.size) else baseFunctionalType.builtIns.getKFunction(
                            parameterVariables.size
                        )
                    else -> null!!
                }.typeConstructor,
                parameterVariables + returnValueVariable.defaultType.asTypeProjection(),
                baseFunctionalType.isMarkedNullable
            )

        csBuilder.addSubtypeConstraint(
            newExpectedType,
            expectedTypeVariable,
            ArgumentConstraintPosition(argument.atom as KotlinCallArgument)
        )

        argument.parameters3 = allParameters
        argument.newExpectedType = newExpectedType
        argument.returnValueVariable = returnValueVariable
        argument.preparedReturnType = returnValueVariable
    }

    private fun Context.dd(
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        diagnosticsHolder: KotlinDiagnosticsHolder,
    ) {
        val postponedArguments = Stack<AtomWithTypeVariableAsExpectedType>().apply {
            addAll(
                getOrderedNotAnalyzedPostponedArguments(topLevelAtoms)
                    .filter { it.expectedType?.constructor is TypeVariableTypeConstructor }
                    .filterIsInstance<AtomWithTypeVariableAsExpectedType>()
            )
        }

        while (true) {
            val res = postponedArguments.any { argument ->
                if (argument is PostponedResolvedAtom) {
                    val a = argument.areParameterTypesLooked
                    collectParameterTypes(argument)

                    if (!a && argument.areParameterTypesLooked) {
                        true
                    } else false
                } else false
            }

            if (res) continue

            break
        }

        if (completionMode == ConstraintSystemCompletionMode.FULL) {
            val postponedArguments2 = getOrderedNotAnalyzedPostponedArguments(topLevelAtoms)
                .filter { it.expectedType?.constructor is TypeVariableTypeConstructor }
                .filterIsInstance<AtomWithTypeVariableAsExpectedType>()

            for (argument in postponedArguments2) {
                if (argument is PostponedResolvedAtom) {
                    fixParameterTypes(argument, diagnosticsHolder)
                }
            }
        }
    }

    private fun Context.runCompletion(
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        topLevelType: UnwrappedType,
        diagnosticsHolder: KotlinDiagnosticsHolder,
        collectVariablesFromContext: Boolean,
        analyze: (PostponedResolvedAtom) -> Unit
    ) {
        while (true) {
            dd(completionMode, topLevelAtoms, diagnosticsHolder)

            /*
             * Step 3: analyze remaining postponed arguments
             */
            val isAnalyzed = analyzePostponedArguments(completionMode, topLevelAtoms, topLevelType, analyze, diagnosticsHolder)

            if (isAnalyzed) {
                continue
            }

            fixReadyVariablesOrReportNotEnoughInformation(completionMode, topLevelAtoms, topLevelType, collectVariablesFromContext)

            if (completionMode == ConstraintSystemCompletionMode.FULL) {
                forceAnalysisPostponedArguments(completionMode, topLevelAtoms, topLevelType, diagnosticsHolder, analyze)
            }

            break
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
        analyze: (PostponedResolvedAtom) -> Unit,
        diagnosticsHolder: KotlinDiagnosticsHolder
    ): Boolean {
        var isAnalyzedGlobal = false

        fun analyzePostponedArgumentWithTypeVariableAsExpectedTypeIfPossible(
            postponedArguments: List<PostponedResolvedAtom>,
            variableForFixation: VariableFixationFinder.VariableForFixation?
        ): Boolean {
            if (variableForFixation == null)
                return false

            val isAnalyzed =
                analyzePostponedArgumentWithTypeVariableAsExpectedType(variableForFixation, postponedArguments, analyze)

            return isAnalyzed
        }

        fun analyzePostponeArgumentIfPossible(postponedArguments: List<PostponedResolvedAtom>, analyze: (PostponedResolvedAtom) -> Unit) =
            postponedArguments.any { argument ->
                ProgressIndicatorAndCompilationCanceledStatus.checkCanceled()
                if (canWeAnalyzeIt(argument)) {
                    analyze(argument)
                    true
                } else false
            }

        while (true) {
            /*
             * We should compute not analyzed postponed arguments on each iteration
             * because analyze the first postponed argument can make possible analysis the second one (and it will appear in postponed argument list)
             */
            val postponedArguments = getOrderedNotAnalyzedPostponedArguments(topLevelAtoms)
            val expectedType = postponedArguments.firstOrNull()?.expectedType ?: break
            val variableForFixation = variableFixationFinder.findFirstVariableForFixation(
                this, listOf(expectedType.constructor), postponedArguments, completionMode, topLevelType
            )
            if (analyzePostponedArgumentWithTypeVariableAsExpectedTypeIfPossible(postponedArguments, variableForFixation)) {
//                fixVariablesInsideFunctionTypeArguments(postponedArguments, topLevelAtoms, completionMode, topLevelType)
                isAnalyzedGlobal = true
                break
            }
            /*
             * We should compute not analyzed postponed arguments on each iteration
             * because analyze the first postponed argument can make possible analysis the second one (and it will appear in postponed argument list)
             */
            fixVariablesInsideFunctionTypeArguments(postponedArguments, topLevelAtoms, completionMode, topLevelType)
            if (analyzePostponeArgumentIfPossible(postponedArguments, analyze)) {
                isAnalyzedGlobal = true
                break
            }

            break
        }

        return isAnalyzedGlobal
    }

    /*
     * returns true -> analyzed
     */
    private fun Context.analyzePostponedArgumentWithTypeVariableAsExpectedType(
        variableForFixation: VariableFixationFinder.VariableForFixation,
        postponedArguments: List<PostponedResolvedAtom>,
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

        return postponedArguments.any { postponedAtom ->
            val shouldAnalyzeByEqualityExpectedTypeToVariable =
                hasProperAtom || !variableForFixation.hasProperConstraint || variableForFixation.hasOnlyTrivialProperConstraint

            if (!shouldAnalyzeByEqualityExpectedTypeToVariable)
                return@any false

            analyze(postponedAtom.expandedExpectedType ?: postponedAtom)

            true
        }
    }

    private fun Context.findFunctionalTypesInConstraints(
        variable: VariableWithConstraints,
        typeVariablesVisited: Set<TypeVariableTypeConstructor> = setOf()
    ): List<KotlinType>? {
        val typeVariableTypeConstructor = variable.typeVariable.freshTypeConstructor() as? TypeVariableTypeConstructor ?: return null
        if (typeVariableTypeConstructor in typeVariablesVisited) return null

        return variable.constraints.mapNotNull { constraint ->
            val type = constraint.type as? KotlinType ?: return@mapNotNull null

            when {
                type.isBuiltinFunctionalTypeOrSubtype -> listOf(type)
                type.constructor in notFixedTypeVariables -> {
                    findFunctionalTypesInConstraints(
                        notFixedTypeVariables.getValue(constraint.type.constructor),
                        typeVariablesVisited + typeVariableTypeConstructor
                    )
                }
                else -> null
            }
        }.flatten()
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