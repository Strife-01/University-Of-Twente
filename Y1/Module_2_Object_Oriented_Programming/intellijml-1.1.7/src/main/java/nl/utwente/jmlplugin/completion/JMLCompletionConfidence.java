package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.CompletionConfidence;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiFile;
import com.intellij.util.ThreeState;
import org.jetbrains.annotations.NotNull;

/**
 * This class tells IntelliJ to always pop-up the completion suggestions.
 *
 * If this is not set to ThreeState.NO the pop-up fails to be aggressive enough, and even with this setting it is a bit
 * less aggressive than you would hope...
 */

public class JMLCompletionConfidence extends CompletionConfidence {

    @Override
    public @NotNull ThreeState shouldSkipAutopopup(@NotNull PsiElement contextElement,
                                                   @NotNull PsiFile psiFile,
                                                   int offset) {
        return ThreeState.NO;
    }
}
