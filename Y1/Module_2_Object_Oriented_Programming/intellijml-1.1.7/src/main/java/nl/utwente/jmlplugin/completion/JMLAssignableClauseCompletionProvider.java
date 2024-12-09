package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.CompletionParameters;
import com.intellij.codeInsight.completion.CompletionProvider;
import com.intellij.codeInsight.completion.CompletionResultSet;
import com.intellij.psi.PsiClass;
import com.intellij.util.ProcessingContext;
import org.jetbrains.annotations.NotNull;

import static nl.utwente.jmlplugin.completion.JMLCompletionUtils.*;
import static nl.utwente.jmlplugin.psi.JMLTokenSet.assignableJavaKeywords;

/**
 * Provides completion suggestions when invoked in assignable clauses.
 * Assignables clauses only need completion for class visible variables and certain JML keywords that are only present
 * in assignable clauses.
 */

public class JMLAssignableClauseCompletionProvider extends CompletionProvider<CompletionParameters> {

    public static final JMLAssignableClauseCompletionProvider INSTANCE = new JMLAssignableClauseCompletionProvider();

    @Override
    protected void addCompletions(@NotNull CompletionParameters parameters, @NotNull ProcessingContext context, @NotNull CompletionResultSet result) {
        final PsiClass psiClass = JMLCompletionUtils.getClass(parameters.getPosition());
        if (psiClass == null) return;

        fillFieldCompletions(psiClass, result, parameters);

        //account for inner classes
        PsiClass enclosingClass = getEnclosingClass(psiClass);
        while (enclosingClass != null) {
            fillFieldCompletions(psiClass, result, parameters);
            enclosingClass = getEnclosingClass(enclosingClass);
        }
        addTokens(assignableJavaKeywords, result);

        sortResults(parameters, result);
    }
}
