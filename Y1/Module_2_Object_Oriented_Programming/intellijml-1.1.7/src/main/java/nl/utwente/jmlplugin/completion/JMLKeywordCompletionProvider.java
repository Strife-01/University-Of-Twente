package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.CompletionParameters;
import com.intellij.codeInsight.completion.CompletionProvider;
import com.intellij.codeInsight.completion.CompletionResultSet;
import com.intellij.codeInsight.lookup.LookupElementBuilder;
import com.intellij.util.ProcessingContext;
import nl.utwente.jmlplugin.annotator.CommentPosition;
import org.jetbrains.annotations.NotNull;

import static nl.utwente.jmlplugin.completion.JMLCompletionUtils.*;
import static nl.utwente.jmlplugin.psi.JMLTokenSet.*;
import static nl.utwente.jmlplugin.psi.JMLTypes.*;

/**
 * Class that provides the list of completable JML keywords.
 *
 * JML expression that can be mixed together are not here as they need to be
 * completed in the mixed Java-JML section of the expressions.
 */

public class JMLKeywordCompletionProvider extends CompletionProvider<CompletionParameters> {

    public static final JMLKeywordCompletionProvider INSTANCE = new JMLKeywordCompletionProvider();

    @Override
    protected void addCompletions(@NotNull CompletionParameters parameters,
                                  @NotNull ProcessingContext context,
                                  @NotNull CompletionResultSet result) {
        final CommentPosition position = getCommentPosition(parameters);

        // figure out in what kind of JML comment you are and fill in the appropriate keyword completions.
        switch (position) {
            case INSIDE_CLASS:
                fillClassInvariantCompletion(result);
                break;
            case ABOVE_CLASS:
                fillClassModifiers(result);
                break;
            case ABOVE_METHOD:
                fillMethodSpecModifiers(result);
            case BEFORE_METHOD_BODY:
                //fallthrough is intentional
                fillMethodSpecCompletions(result);
                break;
            case FIELD:
                fillFieldModifierCompletions(result);
                break;
            case PARAMETER:
                fillParameterCompletions(result);
            case VAR_DECLARATION:
                fillVariableDeclarationCompletions(result);
            case CODE_BLOCK:
                fillCodeBlockCompletions(result);
                break;
            case METHOD_DECLARATION:
                //nothing
            default:
                break;
        }

        sortResults(parameters, result);
    }

    /**
     * Fill in completion for JML comments above variable declarations that are inside method bodies.
     * @param results - completion results holder.
     */

    private static void fillVariableDeclarationCompletions(@NotNull CompletionResultSet results) {
        addTokens(nullable, results);
    }

    /**
     * Fill in completion for JML comments that are associated with method parameters, e.g.
     *
     * public int someMethod(int /*@ COMPLETION_HERE / integerNumber)
     *
     * @param results - completion results holder.
     */

    private static void fillParameterCompletions(@NotNull CompletionResultSet results) {
        addTokens(nullable, results);
    }

    /**
     * Fill in completion for JML comments that are in a code block, usually this means a method body
     * @param results
     */

    private static void fillCodeBlockCompletions(@NotNull CompletionResultSet results) {
        addTokens(codeBlockKeywords, results);
    }

    /**
     * Fill in completion for JML comments that are above a field, usually used to modify the visibility of the field
     * for the JML specification.
     *
     * @param results - completion results holder.
     */

    private static void fillFieldModifierCompletions(@NotNull CompletionResultSet results) {
        addTokens(fieldModifiers, results);
    }

    /**
     * Fill in completion for JML comments that are above a class declaration.
     *
     * @param results - completion results holder.
     */

    private static void fillClassModifiers(@NotNull CompletionResultSet results) {
        addTokens(classModifiers, results);
    }

    /**
     * Fill in JML comment completions for the JML keywords that modify a property of the method (e.g. declaring it pure)
     *
     * @param results - completion result holder.
     */

    private static void fillMethodSpecModifiers(@NotNull CompletionResultSet results) {
        addTokens(methodDeclModifiers, results);
    }

    /**
     * Fill in JML comment completions for the JML keywords that can be the start of the expressions in a JML comment
     * that is above a method (method spec).
     *
     * @param results - completion result holder.
     */

    private static void fillMethodSpecCompletions(@NotNull CompletionResultSet results) {
        addTokens(methodSpecCaseKeywords, results);
        addTokens(also, results);
    }

    /**
     * Fill in JML comment completions for the JML keywords that are appropriate when making an invariant JML comment.
     *
     * @param results - completion result holder.
     */

    private static void fillClassInvariantCompletion(@NotNull CompletionResultSet results) {
        addTokens(visibilityModifiers, results);
        addTokens(invariantModifiers, results);
        //add in invariant itself
        results.addElement(LookupElementBuilder.create(INVARIANT.toString()));
    }
}
