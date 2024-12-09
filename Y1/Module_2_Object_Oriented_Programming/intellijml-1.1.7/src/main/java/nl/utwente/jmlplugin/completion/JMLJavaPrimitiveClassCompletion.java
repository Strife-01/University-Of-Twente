package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.CompletionParameters;
import com.intellij.codeInsight.completion.CompletionProvider;
import com.intellij.codeInsight.completion.CompletionResultSet;
import com.intellij.util.ProcessingContext;
import org.jetbrains.annotations.NotNull;

import static nl.utwente.jmlplugin.completion.JMLCompletionUtils.fillPrimitiveClassCompletions;
import static nl.utwente.jmlplugin.completion.JMLCompletionUtils.sortResults;

public class JMLJavaPrimitiveClassCompletion extends CompletionProvider<CompletionParameters> {

    public static JMLJavaPrimitiveClassCompletion INSTANCE = new JMLJavaPrimitiveClassCompletion();

    @Override
    protected void addCompletions(@NotNull CompletionParameters parameters, @NotNull ProcessingContext context, @NotNull CompletionResultSet result) {
        fillPrimitiveClassCompletions(result);
        sortResults(parameters, result);
    }
}
