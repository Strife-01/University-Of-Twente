package nl.utwente.jmlplugin.completion;

import com.intellij.codeInsight.completion.CompletionParameters;
import com.intellij.codeInsight.completion.CompletionProvider;
import com.intellij.codeInsight.completion.CompletionResultSet;
import com.intellij.psi.*;
import com.intellij.psi.util.PsiUtil;
import com.intellij.util.IncorrectOperationException;
import com.intellij.util.ProcessingContext;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.LinkedList;

import static nl.utwente.jmlplugin.completion.JMLCompletionUtils.*;

/**
 * Provides completions for "." java expressions.
 */

public class JMLJavaDotCompletionProvider extends CompletionProvider<CompletionParameters> {

    private static final String L_PAREN = "(";
    private static final String R_PAREN = ")";
    private static final String DOT = ".";

    public static final JMLJavaDotCompletionProvider INSTANCE = new JMLJavaDotCompletionProvider();

    /**
     * Main method that drives the completion process. This is the method that is called by the completion contributor
     * when it matches the appropriate psi tree pattern to invoke this completion provider.
     *
     * @param parameters - completion context.
     * @param context    - custom data holder, this unused by us.
     * @param result     - completion results holder.
     */

    @Override
    protected void addCompletions(@NotNull CompletionParameters parameters,
                                  @NotNull ProcessingContext context,
                                  @NotNull CompletionResultSet result) {

        //parser has a delay in updating the tree properly, under some conditions JML keywords are
        //not in the tree when they are needed which can throw a null pointer exception, check for it.
        try{
            parameters.getPosition().getPrevSibling().getPrevSibling().getText();
        } catch (NullPointerException e) {
            return;
        }

        //provide support for non-chained dot completion on method parameters.
        if (fillMethodParameterDotCompletions(parameters, result)) return;

        //provide support for \old() and \result non-chained dot completion.
        if (fillJMLKeywordCompletions(parameters, result)) return;


        //construct the text of the preceding expression
        String expressionText;
        try {
            expressionText = getExpressionText(parameters);
        } catch (IllegalStateException | IncorrectOperationException ignored) {
            return;
        }

        if (expressionText == null) {
            return;
        }

        //create an element that can be resolved
        expressionText = expressionText.trim();
        expressionText = replaceJML(expressionText, parameters);
        final PsiExpression parsedExpression = getPsiExpression(expressionText, parameters);

        if (parsedExpression == null) return;

        //resolve the return type of the expression
        final PsiType type = parsedExpression.getType();
        //failed to resolve the return type
        if (type == null) {
            //check for static class reference
            resolveStaticClassReference(expressionText, parameters, result);
            sortResults(parameters, result);
            return;
        }

        //get the class that the return type resolves to
        PsiClass psiClass = PsiUtil.resolveClassInClassTypeOnly(type);

        //primitive types won't resolve to a class, we don't need to autocomplete them
        if (psiClass == null) {
            return;
        }

        //check for super and this completions
        if (checkSuperAndThis(parameters, result, psiClass)) {
            sortResults(parameters, result);
            return;
        }


        //using the class reference fill in the possible completions
        fillClassCompletions(psiClass, result, parameters);
        sortResults(parameters, result);
    }

    /**
     * Provide completions for super and this.
     * @param params - completion context.
     * @param results - completion results holder.
     * @param psiClass - enclosing class (i.e. a reference to the class that <code>this<code/> would resolve to).
     * @return - true if the previous element in the . completion chain was "this" or "super" and completions for the
     * appropriate type could be filled in, false otherwise.
     */

    private static boolean checkSuperAndThis(@NotNull CompletionParameters params, @NotNull CompletionResultSet results, @NotNull final PsiClass psiClass) {
        PsiElement beforeDot = params.getPosition().getPrevSibling().getPrevSibling();

        switch (beforeDot.getText()) {
            case "this":
                fillClassCompletions(psiClass, results, params);
                break;
            case "super":
                fillSuperClassCompletions(results, params);
                break;
            default:
                return false;
        }

        return true;
    }


    /**
     * Fill in completions for static class references.
     *
     * @param text   - raw text of the java expression
     * @param params - completion context
     * @param result - completion results holder.
     */

    private static void resolveStaticClassReference(String text, CompletionParameters params, CompletionResultSet result) {
        final PsiJavaCodeReferenceElement ref = getReference(text, params);
        if (ref == null) return;

        final JavaResolveResult[] resolveResults = ref.multiResolve(true);
        //check the resolve results for what to do
        if (resolveResults.length == 0) {
            //failed to find any possible candidates
            return;
        } else {
            //found some candidates
            if (resolveResults.length == 1) {
                //resolve was unambiguous, but check that this is a class
                final PsiElement elem = resolveResults[0].getElement();
                if (elem instanceof PsiClass) {
                    fillStaticCompletion((PsiClass) elem, result, params);
                }

            } else {
                //we have multiple options, check the import list to see if we know which one is meant
                final PsiImportList importList = getImportList(params);
                boolean match = false;
                PsiClass resolvedClass = null;
                for (JavaResolveResult rez : resolveResults) {
                    if (rez.getElement() instanceof PsiClass) {
                        if (match) {
                            //multiple matches found, ambiguity so return
                            return;
                        } else {
                            //match found
                            match = true;
                            resolvedClass = (PsiClass) rez.getElement();
                        }
                    }
                }

                //fill in the static completion for the resolved class
                fillStaticCompletion(resolvedClass, result, params);
            }
        }
    }

    /**
     * Get a reference for the provided java expression (in string format) that can be later used to resolve references
     * to type and other things.
     *
     * @param text   - raw text of the reference element
     * @param params - completion context
     * @return reference element that can be used to resolve the java code references
     */

    @Nullable
    private static PsiJavaCodeReferenceElement getReference(String text, CompletionParameters params) {
        try {
            return JavaPsiFacade.getInstance(params.getEditor().getProject()).getParserFacade().createReferenceFromText(text, params.getPosition());
        } catch (IncorrectOperationException e) {
            return null;
        }
    }

    /**
     * Returns the text of the incomplete java expression that the completion was called on. If an expression is malformed
     * may return null.
     *
     * @param params - completion context.
     * @return String that represents the java expression that the completion was called on,
     */

    @Nullable
    private static String getExpressionText(@NotNull CompletionParameters params) {
        //check for malformed . completion
        PsiElement elem;
        if ((elem = params.getPosition().getPrevSibling().getPrevSibling()) == null) {
            return null;
        }

        //walk the elements until you captured the relevant expression
        LinkedList<String> result = new LinkedList<>();

        do {
            if (elem.getText().equals(R_PAREN)) {
                elem = closeParentheses(result, elem);
                continue;
            } else if (!(elem.getText().equals(DOT) || elem instanceof PsiIdentifier || elem instanceof PsiWhiteSpace ||
                    elem instanceof PsiKeyword|| elem.getText().equals("\\result") || elem.getText().equals("\\old"))) {
                break;
            }

            result.addFirst(elem.getText());

            elem = elem.getPrevSibling();
            if (elem == null) {
                break;
            }

        } while (true);

        StringBuilder builder = new StringBuilder();
        for (String str : result) {
            builder.append(str);
        }

        return builder.toString();

    }

    /**
     * Method that is meant to traverse through a java expression till it manages to close the current opening parentheses
     * from the right side, this is used to acquired the text between the parentheses traversing the text from right to left.
     *
     * @param builder - string buffer that accumulates all the strings that are necessary for the construction of the
     *                full java expression string.
     * @param elem    - the right parentheses element that opened the parentheses.
     * @return the element immediately after the closing left parentheses.
     */

    private static PsiElement closeParentheses(LinkedList<String> builder, PsiElement elem) {
        int opened = 0;
        do {
            if (elem.getText().equals(L_PAREN)) {
                opened--;
            } else if (elem.getText().equals(R_PAREN)) {
                opened++;
            }

            builder.addFirst(elem.getText());

            elem = elem.getPrevSibling();

            if (elem == null) {
                throw new IllegalStateException("malformed Java expression");
            }

        } while (opened != 0);

        return elem;
    }

    /**
     * Method that replaces all JML \result and \old() expressions with valid Java expressions in the given string.
     * The method replaces \result with either either a null cast to the correct method return type, if the return type
     * is an object or with a literal 0 cast to the correct primitive type. This way a valid Java expression can be
     * obtained for string evaluation.
     *
     * \old() is made valid Java by just simply removing all \old keywords from the string and keeping the parentheses,
     * this is valid java as you can always put parentheses around a java expression and it will still remain valid.
     *
     * This can then be used in string evaluation to retrieve the type of the expression.
     *
     * @param text - text that represents a mixed JML-Java expression.
     *
     * @param params - completion context.
     *
     * @return string where all \old() and \result JML keywords have been replaced by valid Java.
     */

    @NotNull
    private static String replaceJML(@NotNull String text, @NotNull CompletionParameters params) {
        // deep copy the string
        String result = text.concat("");
        //resolve method
        PsiMethod method = getMethodContext(params);

        if (method != null) {
            // method type can be resolved
            final PsiType type = method.getReturnType();

            if (type != null) {
                //check first for primitive type
                PsiType primitive = null;
                try {
                    primitive = JavaPsiFacade.getInstance(params.getEditor().getProject()).getParserFacade().createPrimitiveTypeFromText(type.getCanonicalText());
                } catch (IncorrectOperationException ignored) {

                }

                if (primitive != null && primitive.isValid()) {
                    // any valid non-object literal is castable to any primitive type
                    result = result.replaceAll("\\\\result+", "((" + method.getReturnType().getCanonicalText() + ") 0)");
                } else {
                    // null is castable to any object type
                    result = result.replaceAll("\\\\result+", "((" + method.getReturnType().getCanonicalText() + ") null)");
                }
            }
        }

        // for old just remove the \old part, the parentheses will remain valid Java so they don't have to be removed!
        return result.replaceAll("\\\\old+", "");

    }

}
