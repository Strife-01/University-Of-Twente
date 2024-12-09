package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.CompletionParameters;
import com.intellij.codeInsight.completion.CompletionProvider;
import com.intellij.codeInsight.completion.CompletionResultSet;
import com.intellij.codeInsight.completion.JavaCompletionContributor;
import com.intellij.codeInsight.lookup.LookupElementBuilder;
import com.intellij.psi.*;
import com.intellij.psi.impl.PsiVariableEx;
import com.intellij.psi.impl.source.tree.java.PsiLocalVariableImpl;
import com.intellij.psi.search.GlobalSearchScope;
import com.intellij.psi.util.PsiTreeUtil;
import com.intellij.util.IncorrectOperationException;
import com.intellij.util.ProcessingContext;
import nl.utwente.jmlplugin.annotator.CommentPosition;
import nl.utwente.jmlplugin.annotator.JMLAnnotatorUtil;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.LinkedList;
import java.util.List;

import static nl.utwente.jmlplugin.completion.JMLCompletionUtils.*;

/**
 * Class that is responsible for adding completion contributions for when a completion is called on a lone Java
 * identifier, it resolves static imports, class methods, class field references and adds them to the completion set.
 */

public class JMLJavaIdentifierCompletionProvider extends CompletionProvider<CompletionParameters> {

    public static final JMLJavaIdentifierCompletionProvider INSTANCE = new JMLJavaIdentifierCompletionProvider();
    private static final String EMPTY_STRING = "IntellijIdeaRulezzz";

    /**
     * Main method for filling in completions, this is the method that is called by the completion contributor to
     * get all the completions that this completion provider can give.
     *
     * @param parameters - completion context.
     * @param context    - processing context information, basically you can add your own custom data here to check for
     *                   some complicated situations.
     * @param result     - completion results holder.
     */

    @Override
    protected void addCompletions(@NotNull CompletionParameters parameters, @NotNull ProcessingContext context, @NotNull CompletionResultSet result) {

        //We do not want to autocomplete at number literals
        if (parameters.getPosition().getPrevSibling() != null) {
            if (parameters.getPosition().getPrevSibling().getText().trim().length() != 0) {
                if (Character.isDigit(parameters.getPosition().getPrevSibling().getText().trim().charAt(0))) {
                    return;
                }
            }
        }

        //fill in JML keywords that can be embedded into java
        if (getCommentPosition(parameters) == CommentPosition.ABOVE_METHOD) fillMethodParameterCompletions(parameters, result);
        fillJMLCompletions(parameters, result);

        //check for code block completions
        fillMethodLocalVariables(parameters, result);

        //fill in Java completions
        addFieldAndMethodCompletions(parameters, result);
        //if the identifier starts with a upper case character then add class completions as well, but don't add it if nothing has been typed yet
        if (Character.isUpperCase(parameters.getPosition().getText().trim().charAt(0)) && !parameters.getPosition().getText().equals(EMPTY_STRING)) {
            addJavaClassNameCompletions(parameters, result);
        }

        sortResults(parameters, result);
    }
}
