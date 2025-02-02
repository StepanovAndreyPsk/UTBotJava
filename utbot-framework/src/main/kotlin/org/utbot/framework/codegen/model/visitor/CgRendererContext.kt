package org.utbot.framework.codegen.model.visitor

import org.utbot.framework.codegen.model.UtilClassKind
import org.utbot.framework.codegen.model.UtilClassKind.Companion.utilsPackageFullName
import org.utbot.framework.codegen.model.constructor.builtin.UtilMethodProvider
import org.utbot.framework.codegen.model.constructor.builtin.selectUtilClassId
import org.utbot.framework.codegen.model.constructor.builtin.utJavaUtilsClassId
import org.utbot.framework.codegen.model.constructor.builtin.utKotlinUtilsClassId
import org.utbot.framework.codegen.model.constructor.context.CgContext
import org.utbot.framework.plugin.api.ClassId
import org.utbot.framework.plugin.api.CgLanguageAssistant
import org.utbot.framework.plugin.api.CodegenLanguage
import org.utbot.framework.plugin.api.MethodId
import org.utbot.framework.plugin.api.MockFramework

/**
 * Information from [CgContext] that is relevant for the renderer.
 * Not all the information from [CgContext] is required to render a class,
 * so this more lightweight context is created for this purpose.
 */
class CgRendererContext(
    val shouldOptimizeImports: Boolean,
    val importedClasses: Set<ClassId>,
    val importedStaticMethods: Set<MethodId>,
    val classPackageName: String,
    val generatedClass: ClassId,
    val utilMethodProvider: UtilMethodProvider,
    val codegenLanguage: CodegenLanguage,
    val mockFrameworkUsed: Boolean,
    val mockFramework: MockFramework,
    val cgLanguageAssistant: CgLanguageAssistant,
) {
    companion object {
        fun fromCgContext(context: CgContext): CgRendererContext {
            return CgRendererContext(
                shouldOptimizeImports = context.shouldOptimizeImports,
                importedClasses = context.importedClasses,
                importedStaticMethods = context.importedStaticMethods,
                classPackageName = context.testClassPackageName,
                generatedClass = context.outerMostTestClass,
                utilMethodProvider = context.utilMethodProvider,
                codegenLanguage = context.codegenLanguage,
                cgLanguageAssistant = context.cgLanguageAssistant,
                mockFrameworkUsed = context.mockFrameworkUsed,
                mockFramework = context.mockFramework
            )
        }

        fun fromUtilClassKind(utilClassKind: UtilClassKind, language: CodegenLanguage): CgRendererContext {
            return CgRendererContext(
                shouldOptimizeImports = false,
                importedClasses = emptySet(),
                importedStaticMethods = emptySet(),
                classPackageName = utilsPackageFullName(language),
                generatedClass = selectUtilClassId(language),
                utilMethodProvider = utilClassKind.utilMethodProvider,
                codegenLanguage = language,
                mockFrameworkUsed = utilClassKind.mockFrameworkUsed,
                mockFramework = utilClassKind.mockFramework,
                cgLanguageAssistant = CgLanguageAssistant.getByCodegenLanguage(language),
            )
        }
    }
}