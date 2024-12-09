package nl.utwente.jmlplugin.annotator;

import com.intellij.lang.annotation.AnnotationHolder;
import com.intellij.lang.annotation.HighlightSeverity;
import com.intellij.openapi.application.ApplicationManager;
import com.intellij.openapi.editor.DefaultLanguageHighlighterColors;
import com.intellij.openapi.editor.colors.EditorColorsManager;
import com.intellij.openapi.editor.markup.TextAttributes;
import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiErrorElement;
import com.intellij.psi.util.PsiUtil;
import nl.utwente.jmlplugin.psi.*;
import org.jetbrains.annotations.NotNull;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import static com.intellij.psi.util.PsiTreeUtil.*;

/**
 * Checks the tree for syntax errors
 */
public class JMLSyntaxAnnotator {

    /**
     * Annotates the elements on syntax errors
     *
     * @param element the element we are checking
     * @param holder  the Annotation holder
     * @return false if the element has a syntax error
     */
    public static boolean annotateSyntax(@NotNull PsiElement element, @NotNull AnnotationHolder holder) {
        if (element instanceof JMLFile) {
            // find all parser errors
            Collection<PsiErrorElement> errorElements = findChildrenOfType(element, PsiErrorElement.class);
            for (PsiErrorElement elem : errorElements) {
                if (elem.getFirstChild() != null) {
                    // has child so can place error on the position of the error element
                    annotateSyntaxError(elem, elem.getTextRange(), false, holder);
                } else {
                    // no child, so place the error on the last character of the previous element
                    annotateSyntaxError(elem, PsiUtil.getElementAtOffset((JMLFile) element,
                            elem.getTextRange().getStartOffset() - 1).getTextRange(), true, holder);
                }
            }
            if (errorElements.size() > 0 && !ApplicationManager.getApplication().isUnitTestMode()) {
                // set the foreground color to the default comment color, as it contains syntax errors
                TextAttributes textAttributes = new TextAttributes();
                textAttributes.setForegroundColor(EditorColorsManager.getInstance().getSchemeForCurrentUITheme()
                        .getAttributes(DefaultLanguageHighlighterColors.BLOCK_COMMENT).getForegroundColor());
                holder.newSilentAnnotation(
                        new HighlightSeverity("", 1))
                        .enforcedTextAttributes(textAttributes)
                        .create();
            }
            return errorElements.size() == 0;
        }
        return true;
    }

    /**
     * Puts an appropriate error message in the annotation holder.
     *
     * @param element the PsiErrorElement for which we creating an error message
     * @param range   the range on which the error message needs to be placed
     * @param holder  holds the current annotations
     */
    private static void annotateSyntaxError(PsiErrorElement element, TextRange range, boolean errorPutOnPrevious, AnnotationHolder holder) {
        String errorString = element.getErrorDescription();
        String extraText;
        if (checkRequiresNotAsFirstClauseOnError(element)) {
            errorString = ErrorMessages.REQUIRES_FIRST;
        } else if (checkModifierBeforeSpecClausesOnError(element)) {
            errorString = ErrorMessages.NO_MODIFIER_BEFORE_SPEC;
        } else if (checkSignalsWithoutParens(element)) {
            errorString = ErrorMessages.SIGNALS_WITHOUT_PARENS;
        } else if (checkRefSquareBraceButNotStar(element)) {
            errorString = ErrorMessages.SQUARE_BRACKET_BUT_NOT_STAR;
        } else if ((extraText = checkSignalsOnlyReferenceExpected(element)) != null) {
            errorString = extraText;
        } else {
            errorString = editErrorString(errorString);
        }
        if (errorPutOnPrevious) {
            //noinspection DialogTitleCapitalization
            errorString = errorString.replace("expected", "expected after this token");
        }
        holder.newAnnotation(HighlightSeverity.ERROR, errorString).range(range != null ? range : element.getTextRange()).create();
    }

    /**
     * Checks whether the requires keyword was put after other specification clauses
     *
     * @param element the PsiErrorElement for which we are checking
     * @return true if this error has occurred
     */
    private static boolean checkRequiresNotAsFirstClauseOnError(PsiErrorElement element) {
        if (element.getFirstChild() != null &&
                (element.getFirstChild().getNode().getElementType() == JMLTypes.REQUIRES || element.getFirstChild().getNode().getElementType() == JMLTypes.PRE)) {
            // find the JML root and check that the comment is a method specification,
            // then we know that it is not just because requires is just placed anywhere random
            PsiElement jmlRoot = skipWhitespacesAndCommentsBackward(element);
            return jmlRoot instanceof JMLJmlSpecification
                    && findChildOfType(jmlRoot, JMLMethodSpec.class) != null;
        }
        return false;
    }


    /**
     * Checks whether modifiers have been placed after specification cases
     *
     * @param element the PsiErrorElement for which we are checking
     * @return A String containing the names of the modifiers that are in the wrong position, or
     * null if this error has not occurred.
     */
    private static boolean checkModifierBeforeSpecClausesOnError(PsiErrorElement element) {
        // unfortunately it shows the error on the spec clause instead of on the modifier,
        // due to how the parser parses it
        if (element.getFirstChild() != null && JMLTokenSet.methodSpecCaseKeywords.contains(
                element.getFirstChild().getNode().getElementType())) {
            // find the JML root and check that the comment is a method specification,
            // then we know that it is not just because requires is just placed anywhere random
            PsiElement jmlRoot = skipWhitespacesAndCommentsBackward(element);
            return jmlRoot instanceof JMLJmlSpecification
                    && findChildOfType(jmlRoot, JMLModifiers.class) != null;
        }
        return false;
    }

    /**
     * Checks whether there is something else than '*' in between the braces, which is unsupported by us
     *
     * @param element the error element
     * @return true if this error has occurred
     */
    private static boolean checkRefSquareBraceButNotStar(PsiErrorElement element) {
        // check if error message contains "expected" and "asterisk" and whether
        // there was a [ before it
        if (element.getErrorDescription().contains(" expected")) {
            String expected = element.getErrorDescription().split(" expected")[0];
            PsiElement prevElem = skipWhitespacesAndCommentsBackward(element);
            return prevElem != null && expected.equals("asterisk") && prevElem.getNode().getElementType() == JMLTypes.L_SQ_BRAC;
        }
        return false;
    }

    /**
     * Checks whether signals_only was written without any exception references
     *
     * @param element the error element
     * @return true if this error has occurred
     */
    private static String checkSignalsOnlyReferenceExpected(PsiErrorElement element) {
        String errorString = element.getErrorDescription();
        if (errorString.contains("identifier expected")) {
            // See if there is something that looks like a signals_only clause in front
            PsiElement prevSibling = skipWhitespacesAndCommentsBackward(element);
            while (prevSibling != null && !JMLTokenSet.methodSpecCaseKeywords.
                    contains(prevSibling.getNode().getElementType())) {
                prevSibling = skipWhitespacesAndCommentsBackward(prevSibling);
            }
            // if there was signals_only in front, if there is a second half to the message, add it to our custom error
            if (prevSibling != null && prevSibling.getNode().getElementType() == JMLTypes.SIGNALS_ONLY) {
                String[] split = errorString.split(" expected");
                return ErrorMessages.EXCEPTION_REFERENCE_EXPECTED + (split.length == 2 ? split[1] : "");
            }
        }
        return null;
    }


    /**
     * Checks whether there is a signals clause without parentheses
     *
     * @param element the PsiErrorElement for which we are checking
     * @return true if the error has occurred.
     */
    private static boolean checkSignalsWithoutParens(PsiErrorElement element) {
        // check if it is expecting "(" or ")"
        String errorString = element.getErrorDescription();
        if (errorString.contains(" expected")) {
            String expected = errorString.split(" expected")[0];
            if (expected.contains("left parenthesis") || expected.contains("right parenthesis")) {
                // See if there is something that looks like a signals clause in front
                // by looking for the token named "signals".
                PsiElement prevSibling = skipWhitespacesAndCommentsBackward(element);
                // keep looking until we come across a clause, as we only want to see if
                // the last clause is signals
                while (prevSibling != null && !JMLTokenSet.methodSpecCaseKeywords.
                        contains(prevSibling.getNode().getElementType())) {
                    prevSibling = skipWhitespacesAndCommentsBackward(prevSibling);
                }
                return prevSibling != null && prevSibling.getNode().getElementType() == JMLTypes.SIGNALS;
            }
        }
        return false;
    }

    /**
     * Makes the standard error message a bit prettier
     *
     * @param errorString The generated error string by the parser
     * @return returns the error message to display or null if no replacement occurred.
     */
    private static String editErrorString(String errorString) {
        if (errorString.contains(" expected")) {
            String[] errorStrings = errorString.split(" expected");
            // it is contains at least 3 modifiers, then it is safe to assume it is expected any modifiers,
            // so replace all of those with the word "modifiers"
            if (errorStrings[0].contains("helper") && errorStrings[0].contains("instance") && errorStrings[0].contains("nullable")) {
                errorStrings[0] = ErrorMessages.replaceAllModifiers(errorStrings[0]);
            }
            // this is added by the parser, it means we need to show an error message that
            // the quantified expression needs parentheses around itself
            else if (errorStrings[0].contains("NO_LPAREN_BEFORE_QUANTIFIER")) {
                return ErrorMessages.NO_PARENS_AROUND_QUANTIFIER;
            }
            // replace some ugly token text representations, mainly tokens coming from java
            for (Map.Entry<String, String> entry : ErrorMessages.internalToDisplayText.entrySet()) {
                errorStrings[0] = errorStrings[0].replace(entry.getKey(), entry.getValue());
            }
            // join the (replaced) left side of the string with the (optional) right side
            errorString = errorStrings[0] + " expected" + (errorStrings.length == 2 ? errorStrings[1] : "");
        }
        // capitalize first letter
        return errorString.trim().substring(0, 1).toUpperCase() + errorString.substring(1).toLowerCase();
    }


}
