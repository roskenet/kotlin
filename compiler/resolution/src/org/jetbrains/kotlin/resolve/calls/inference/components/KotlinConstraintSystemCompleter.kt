/*
 * Copyright 2000-2018 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.resolve.calls.inference.components

import org.jetbrains.kotlin.builtins.*
import org.jetbrains.kotlin.descriptors.annotations.Annotations
import org.jetbrains.kotlin.descriptors.annotations.BuiltInAnnotationDescriptor
import org.jetbrains.kotlin.descriptors.annotations.FilteredAnnotations
import org.jetbrains.kotlin.resolve.calls.components.transformToResolvedLambda
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

    private fun extractParameterTypesFromDeclaration(atom: ResolutionAtom): List<KotlinType?>? {
        return if (atom is FunctionExpression && atom.receiverType != null) {
            listOf(atom.receiverType) + atom.parametersTypes.map { it }
        } else if (atom is LambdaKotlinCallArgument) atom.parametersTypes?.map { it }
        else null
    }

    private fun Context.extractParameterTypesFromConstraints(
        expectedTypeVariable: TypeConstructor
    ): ExtractedParameterTypesInfo? {
        if (expectedTypeVariable !in notFixedTypeVariables) return null

        val foundFunctionalTypes = findFunctionalTypesInConstraints(notFixedTypeVariables.getValue(expectedTypeVariable)) ?: return null

        return ExtractedParameterTypesInfo(
            null,
            foundFunctionalTypes.map { it.arguments.dropLast(1).map { it.type } }.toSet(),
            Annotations.create(foundFunctionalTypes.map { it.annotations }.flatten()),
            foundFunctionalTypes.isNotEmpty() && foundFunctionalTypes.all { it.isSuspendFunctionTypeOrSubtype },
            foundFunctionalTypes.isNotEmpty() && foundFunctionalTypes.all { it.isMarkedNullable }
        )
    }

    private fun Context.fixVariablesForParameterTypes(argument: PostponedAtomWithRevisableExpectedType) {
        if (argument !is PostponedResolvedAtom) return

        if (argument.parameters3 != null) {
            argument.revisedExpectedType?.arguments?.dropLast(1)?.forEachIndexed { i, el ->
                if (argument.parameters3!![i].all { it != null }) {
                    fixVariable(this, notFixedTypeVariables.getValue(el.type.constructor), listOf(argument))
                }
            }
        }
    }

    private fun Context.transformToAtomWithFunctionalExpectedType(
        argument: PostponedAtomWithRevisableExpectedType,
        diagnosticsHolder: KotlinDiagnosticsHolder
    ) {
        if (argument.parameters3 != null) {
            when (argument) {
                is PostponedCallableReferenceAtom -> {
                    PostponedCallableReferenceAtom(
                        EagerCallableReferenceAtom(argument.atom, argument.revisedExpectedType)
                    ).also {
                        argument.setAnalyzedResults(null, listOf(it))
                    }
                }
                is LambdaWithTypeVariableAsExpectedTypeAtom ->
                    argument.transformToResolvedLambda(
                        (this as NewConstraintSystem).getBuilder(),
                        diagnosticsHolder,
                        argument.revisedExpectedType,
                        argument.revisedExpectedType?.let { notFixedTypeVariables.getValue(it.arguments.last().type.constructor).typeVariable as TypeVariableForLambdaReturnType }
                    )
                else -> null!!
            }
        }
    }

    data class ExtractedParameterTypesInfo(
        val parametersFromDeclaration: List<KotlinType?>?,
        val parametersFromConstraints: Set<List<KotlinType>>?,
        val annotations: Annotations,
        val isSuspend: Boolean,
        val isNullable: Boolean
    ) {
        companion object {
            val EMPTY = ExtractedParameterTypesInfo(null, null, Annotations.EMPTY, false, false)
        }
    }

    private fun Context.collectParameterTypes(argument: PostponedAtomWithRevisableExpectedType): ExtractedParameterTypesInfo? {
        if (argument.areParameterTypesLooked) return null

        val expectedType = argument.expectedType ?: return null
        val atom = argument.atom

        val parameterTypesInfoFromConstraints = extractParameterTypesFromConstraints(expectedType.constructor)

        return ExtractedParameterTypesInfo(
            parametersFromDeclaration = extractParameterTypesFromDeclaration(atom),
            parametersFromConstraints = parameterTypesInfoFromConstraints?.parametersFromConstraints,
            annotations = parameterTypesInfoFromConstraints?.annotations ?: Annotations.EMPTY,
            isSuspend = parameterTypesInfoFromConstraints?.isSuspend ?: false,
            isNullable = parameterTypesInfoFromConstraints?.isNullable ?: false,
        )
    }

    private fun Context.addConstraintForParameters(
        argument: PostponedAtomWithRevisableExpectedType,
        extractedParameterTypesInfo: ExtractedParameterTypesInfo
    ) {
         val al = extractedParameterTypesInfo.run {
             if (!parametersFromDeclaration.isNullOrEmpty() && !parametersFromConstraints.isNullOrEmpty()) {
                 parametersFromConstraints + listOf(
                     if (parametersFromConstraints.isNotEmpty() && parametersFromConstraints.first().size - 1 > parametersFromDeclaration.size) {
                         listOf(null) + parametersFromDeclaration
                     } else {
                         parametersFromDeclaration
                     }
                 )
             } else if (!parametersFromDeclaration.isNullOrEmpty()) {
                 listOf(parametersFromDeclaration)
             } else parametersFromConstraints
         } ?: return

        if (al.isEmpty()) return

        argument.areParameterTypesLooked = true

        val parameterTypes = al.first().indices.map { i -> al.map { it.getOrNull(i) } }

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
        val parameterVariables = parameterTypes.map { types ->
            val parameterTypeVariable = typeVariableCreatorForInputType().apply { csBuilder.registerVariable(this) }

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
        val isExtensionFunctionType = extractedParameterTypesInfo.annotations.hasAnnotation(KotlinBuiltIns.FQ_NAMES.extensionFunctionType)

        val newExpectedType =
            KotlinTypeFactory.simpleType(
                if (isExtensionFunctionType && extractedParameterTypesInfo.parametersFromDeclaration?.size == (extractedParameterTypesInfo.parametersFromConstraints?.firstOrNull()?.size ?: 0) && extractedParameterTypesInfo.parametersFromDeclaration.all { it != null } && extractedParameterTypesInfo.parametersFromConstraints?.firstOrNull()?.firstOrNull() == extractedParameterTypesInfo.parametersFromDeclaration.firstOrNull()) {
                    FilteredAnnotations(extractedParameterTypesInfo.annotations, true) { it != KotlinBuiltIns.FQ_NAMES.extensionFunctionType }
                } else if (argument.atom is FunctionExpression && (argument.atom as FunctionExpression).receiverType != null) {
                    Annotations.create(extractedParameterTypesInfo.annotations + BuiltInAnnotationDescriptor(expectedTypeVariable.builtIns, KotlinBuiltIns.FQ_NAMES.extensionFunctionType, emptyMap()))
                } else extractedParameterTypesInfo.annotations,
                when (argument) {
                    is LambdaWithTypeVariableAsExpectedTypeAtom ->
                        if (extractedParameterTypesInfo.isSuspend) expectedTypeVariable.builtIns.getSuspendFunction(parameterVariables.size) else expectedTypeVariable.builtIns.getFunction(
                            parameterVariables.size
                        )
                    is PostponedCallableReferenceAtom ->
                        if (extractedParameterTypesInfo.isSuspend) expectedTypeVariable.builtIns.getKSuspendFunction(parameterVariables.size) else expectedTypeVariable.builtIns.getKFunction(
                            parameterVariables.size
                        )
                    else -> null!!
                }.typeConstructor,
                parameterVariables + returnValueVariable.defaultType.asTypeProjection(),
                extractedParameterTypesInfo.isNullable
            )

        csBuilder.addSubtypeConstraint(
            newExpectedType,
            expectedTypeVariable,
            ArgumentConstraintPosition(argument.atom as KotlinCallArgument)
        )

        argument.parameters3 = parameterTypes
        argument.revisedExpectedType = newExpectedType
    }

    private fun Context.collectParameterTypesForAllArguments(postponedArguments: List<PostponedAtomWithRevisableExpectedType>) {
        val postponedArgumentsFiltered = Stack<PostponedAtomWithRevisableExpectedType>().apply { addAll(postponedArguments.filter { it.expectedType?.constructor is TypeVariableTypeConstructor }) }

        while (true) {
            val res = postponedArgumentsFiltered.any { argument ->
                val a = argument.areParameterTypesLooked
                val info = collectParameterTypes(argument)

                if (info != null) {
                    addConstraintForParameters(argument, info)
                }

                !a && argument.areParameterTypesLooked
            }

            if (res) continue

            break
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
            val postponedArguments = getOrderedNotAnalyzedPostponedArguments(topLevelAtoms)

            // Stage 1: collect parameter types from declaration and constraints
            collectParameterTypesForAllArguments(postponedArguments.filterIsInstance<PostponedAtomWithRevisableExpectedType>())

            // Stage 2: fix variables for parameter types
            if (completionMode == ConstraintSystemCompletionMode.FULL) {
                val postponedArguments2 = postponedArguments
                    .filter { it.expectedType?.constructor is TypeVariableTypeConstructor }
                    .filterIsInstance<PostponedAtomWithRevisableExpectedType>()

                for (argument in postponedArguments2) {
                    fixVariablesForParameterTypes(argument)
                    transformToAtomWithFunctionalExpectedType(argument, diagnosticsHolder)
                }
            }

            /*
             * We should get not analyzed postponed arguments again because they can be changed by the stage of fixation type variables for parameters,
             * namely, postponed arguments with type variable as expected type can be replaced with resolved postponed arguments with functional expected type.
             *
             * See `transformToAtomWithFunctionalExpectedType`
             */
            val revisedPostponedArguments = getOrderedNotAnalyzedPostponedArguments(topLevelAtoms)

            // Stage 3: analyze the first ready postponed argument and rerun stages if it has been done
            if (analyzeNextReadyPostponedArgument(completionMode, topLevelAtoms, topLevelType, revisedPostponedArguments, analyze))
                continue

            fixReadyVariablesOrReportNotEnoughInformation(completionMode, topLevelAtoms, topLevelType, collectVariablesFromContext, revisedPostponedArguments)

            if (completionMode == ConstraintSystemCompletionMode.FULL) {
                // Force analysis remaining postponed arguments
                revisedPostponedArguments.forEach(analyze)

                // Rerun stages if there are some not fixed type variables within the current postponed arguments
                if (notFixedTypeVariables.isNotEmpty() && postponedTypeVariables.isEmpty())
                    continue
            }

            break
        }
    }

    private fun Context.fixReadyVariablesOrReportNotEnoughInformation(
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        topLevelType: UnwrappedType,
        collectVariablesFromContext: Boolean,
        postponedArguments: List<PostponedResolvedAtom>
    ) {
        while (true) {
            val allTypeVariables = getOrderedAllTypeVariables(collectVariablesFromContext, topLevelAtoms)
            val variableForFixation = variableFixationFinder.findFirstVariableForFixation(
                this, allTypeVariables, postponedArguments, completionMode, topLevelType
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

    private fun Context.analyzeNextReadyPostponedArgument(
        completionMode: ConstraintSystemCompletionMode,
        topLevelAtoms: List<ResolvedAtom>,
        topLevelType: UnwrappedType,
        postponedArguments: List<PostponedResolvedAtom>,
        analyze: (PostponedResolvedAtom) -> Unit
    ): Boolean {
        val argumentWithTypeVariableAsExpectedType =
            findSuitablePostponedArgumentWithTypeVariableAsExpectedType(postponedArguments, topLevelType, completionMode)

        if (argumentWithTypeVariableAsExpectedType != null) {
            analyze(argumentWithTypeVariableAsExpectedType)
            return true
        }

        postponedArguments.forEach { argument ->
            if (argument.expectedType?.isBuiltinFunctionalType == true && argument.expectedType!!.arguments.size > 1) {
                fixVariablesInsideTypes(argument.expectedType!!.arguments.dropLast(1).map { it.type }, topLevelAtoms, completionMode, topLevelType)
            }
        }

        val argumentWithFixedOrPostponedInputTypes = findPostponedArgumentWithFixedOrPostponedInputTypes(postponedArguments)

        if (argumentWithFixedOrPostponedInputTypes != null) {
            analyze(argumentWithFixedOrPostponedInputTypes)
            return true
        }

        return false
    }

    private fun Context.findPostponedArgumentWithFixedOrPostponedInputTypes(postponedArguments: List<PostponedResolvedAtom>) =
        postponedArguments.find { argument ->
            argument.inputTypes.all { containsOnlyFixedOrPostponedVariables(it) }
        }

    private fun Context.findSuitablePostponedArgumentWithTypeVariableAsExpectedType(
        postponedArguments: List<PostponedResolvedAtom>,
        topLevelType: UnwrappedType,
        completionMode: ConstraintSystemCompletionMode,
    ) = postponedArguments.filter { it.expectedType?.constructor is TypeVariableTypeConstructor }.find { postponedAtom ->
        val expectedType = postponedAtom.expectedType ?: return@find false
        val variableForFixation = variableFixationFinder.findFirstVariableForFixation(
            this, listOf(expectedType.constructor), listOf(postponedAtom), completionMode, topLevelType
        )
        val variable = variableForFixation?.variable ?: return@find false
        val hasProperAtom =
            (postponedAtom is LambdaWithTypeVariableAsExpectedTypeAtom || postponedAtom is PostponedCallableReferenceAtom) &&
                    postponedAtom.expectedType?.constructor == variable

        hasProperAtom || !variableForFixation.hasProperConstraint || variableForFixation.hasOnlyTrivialProperConstraint
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
                is LambdaWithTypeVariableAsExpectedTypeAtom ->
                    revisedExpectedType?.arguments?.map { it.type.constructor }?.filterIsInstance<TypeVariableTypeConstructor>().orEmpty()
                is ResolvedCallAtom -> freshVariablesSubstitutor.freshVariables.map { it.freshTypeConstructor }
                is PostponedCallableReferenceAtom ->
                    revisedExpectedType?.arguments?.map { it.type.constructor }?.filterIsInstance<TypeVariableTypeConstructor>().orEmpty() + candidate?.freshSubstitutor?.freshVariables?.map { it.freshTypeConstructor }.orEmpty()
                is ResolvedCallableReferenceAtom -> candidate?.freshSubstitutor?.freshVariables?.map { it.freshTypeConstructor }.orEmpty()
                is ResolvedLambdaAtom -> listOfNotNull(typeVariableForLambdaReturnType?.freshTypeConstructor)
                else -> emptyList()
            }

            typeVariables.mapNotNullTo(to) {
                it.takeIf { notFixedTypeVariables.containsKey(it) }
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