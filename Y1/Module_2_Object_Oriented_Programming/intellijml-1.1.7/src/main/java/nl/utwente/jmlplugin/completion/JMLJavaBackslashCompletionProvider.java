package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.*;
import com.intellij.codeInsight.lookup.LookupElement;
import com.intellij.codeInsight.lookup.LookupElementBuilder;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.tree.TokenSet;
import com.intellij.util.ProcessingContext;
import nl.utwente.jmlplugin.psi.JMLTokenSet;
import org.jetbrains.annotations.NotNull;

import static nl.utwente.jmlplugin.completion.JMLCompletionUtils.*;
import static nl.utwente.jmlplugin.psi.JMLTokenSet.*;

/**
 * Provides completion for \jmlkeywords in Java+JML expressions. This needs to be separate because the parser errors out on \ in java expressions
 * as it tries to read it as Java, so you end up getting \ + jmlkeyword instead of \jmlkeyword.
 *
 * This isn't context aware as making this context aware would require heavy string matching due to the messed up parse
 * tree (because \ is seen as a error element) and is too expensive to implement for something intended to be snappy.
 */

public class JMLJavaBackslashCompletionProvider extends CompletionProvider<CompletionParameters> {

    public static final JMLJavaBackslashCompletionProvider INSTANCE = new JMLJavaBackslashCompletionProvider();

    @Override
    protected void addCompletions(@NotNull CompletionParameters parameters, @NotNull ProcessingContext context, @NotNull CompletionResultSet result) {
        addBackslashTokens(old, result);
        addBackslashTokens(JMLTokenSet.result, result);
        addBackslashTokens(assignableJavaKeywords, result);
    }

    /**
     * Modified token addition method meant for \jmlkeywords insertions as without this method insertions
     * end up inserting \ twice.
     * @param set - token set that needs its string value extracted and put into the completion results.
     * @param results - completion results holder.
     */

    private static void addBackslashTokens(@NotNull TokenSet set, @NotNull CompletionResultSet results) {
        for (IElementType token:set.getTypes()) {
            String tokenText = token.toString();
            if (tokenNeedsParentheses(tokenText)) tokenText = tokenText + "()";

            results.addElement(PrioritizedLookupElement.withPriority(LookupElementBuilder.create(tokenText).withInsertHandler(new InsertHandler<LookupElement>() {
                @Override
                public void handleInsert(@NotNull InsertionContext context, @NotNull LookupElement item) {
                    context.setAddCompletionChar(false);
                    context.commitDocument();
                    context.getDocument().deleteString(context.getStartOffset(), context.getStartOffset() + 1);
                }
            }), JMLCompletionWeights.KEYWORD.getWeight()));

        }
    }

}
