package org.utbot.intellij.plugin.ui.actions

import com.intellij.openapi.actionSystem.AnAction
import com.intellij.openapi.actionSystem.AnActionEvent
import org.utbot.intellij.plugin.language.agnostic.LanguageAssistant

class GenerateTestsAction : AnAction() {
    override fun actionPerformed(e: AnActionEvent) {
        LanguageAssistant.get(e)?.actionPerformed(e)
    }

    override fun update(e: AnActionEvent) {
        LanguageAssistant.get(e)?.update(e)
    }
}