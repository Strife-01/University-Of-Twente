package nl.utwente.jmlplugin.annotator;

import com.intellij.lang.java.JavaLanguage;
import com.intellij.psi.*;
import com.intellij.psi.tree.IElementType;
import com.intellij.psi.tree.TokenSet;
import com.intellij.psi.util.PsiTreeUtil;
import nl.utwente.jmlplugin.psi.JMLModifiers;
import nl.utwente.jmlplugin.psi.JMLTokenSet;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Util class for the annotators containing lookup functions for JML comments
 */
public class JMLAnnotatorUtil {
    public static final String ALL_MODIFIERS_REGEX;

    // make a regex string that can match any JML modifier
    static {
        StringBuilder regex = new StringBuilder("(");
        for (IElementType modifier : JMLTokenSet.allModifiers.getTypes()) {
            regex.append(modifier.toString()).append("|");
        }
        ALL_MODIFIERS_REGEX = regex.replace(regex.length() - 1, regex.length(), ")").toString();
    }

    /**
     * Gets the Java context element of the specification
     *
     * @param element Any JML PsiElement
     * @return the Java PSI context element (such as PsiClass or PsiMethod, etc.)
     */
    public static PsiElement getJavaContext(PsiElement element) {
        PsiComment commentContext = getCommentContext(element);
        return commentContext != null ? commentContext.getParent() : null;
    }

    /**
     * Gets the comment context element of the specification
     *
     * @param element JML PsiElement
     * @return the PsiComment context element
     */
    public static PsiComment getCommentContext(PsiElement element) {
        return PsiTreeUtil.getContextOfType(element, PsiComment.class);
    }

    /**
     * Generates a list of all comments that come before the current comment
     *
     * @param myComment     the comment to look backwards from
     * @param alsoAddMyself whether myComment should be included in the resulting list
     * @return a list of all comments that come before the current comment, possible including myComment as well
     */
    public static ArrayList<PsiComment> collectPreviousComments(PsiComment myComment, boolean alsoAddMyself) {
        ArrayList<PsiComment> resultList = new ArrayList<>();
        if (myComment == null) return resultList;
        PsiElement parent = myComment.getParent();

        // get all comment backwards from currentComment, we do this always because all functions in the class want those for sure
        PsiElement currentElement = (alsoAddMyself ? myComment : myComment.getPrevSibling());
        while (true) {
            if (currentElement instanceof PsiComment) {
                resultList.add((PsiComment) currentElement);
            }
            // max 1 newline is allowed between comments for them to still belong to the same group,
            // unless they are a field or a method, then something other than whitespace is also allowed
            else if (currentElement == null || !(parent instanceof PsiField || parent instanceof PsiMethod || (currentElement instanceof PsiWhiteSpace
                    && currentElement.getText().matches("^[ \t\u00A0]*(\n|\r\n)?[ \t\u00A0]*$")))) {
                // for local variables and parameters, it could be inside the declaration or before, if we are inside, also go before
                currentElement = null;
                if (parent instanceof PsiLocalVariable) {
                    currentElement = parent.getParent();
                    parent = null;
                } else if (parent instanceof PsiParameter) {
                    currentElement = parent;
                    parent = null;
                }
                // was not inside local variable or parameter
                if (currentElement == null) {
                    break;
                }
            }
            currentElement = currentElement.getPrevSibling();
        }
        return resultList;
    }

    /**
     * Checks whether the previous comments matches the regex
     *
     * @param element                the element from which to start the search
     * @param regex                  the regex that should be matched
     * @param doNotCountMyself       if true, at least 2 occurrences need to be found instead of 1
     * @param alsoSearchMyOwnComment if true, the current comment is included in the search
     * @return true if the regex could be matched in the previous comments
     */
    public static boolean doPrevCommentsContain(PsiElement element, String regex, boolean doNotCountMyself, boolean alsoSearchMyOwnComment) {
        PsiComment myComment = getCommentContext(element);
        ArrayList<PsiComment> comments = collectPreviousComments(myComment, alsoSearchMyOwnComment);
        return countTextMatchesAcrossComments(comments, regex, (doNotCountMyself ? 2 : 1)) >= (doNotCountMyself ? 2 : 1);
    }

    /**
     * Checks whether the regex can be matched in comment containing an invariant
     *
     * @param element the element to search
     * @param tokens  the tokens out of which one needs to match with the token-type of the modifier
     * @return true if the regex could be matched in the comment
     */
    public static boolean doPrevInvariantModifiersContain(PsiElement element, TokenSet tokens) {
        if (element == null) return false;
        for (PsiElement currentElement = element.getPrevSibling(); currentElement != null; currentElement = currentElement.getPrevSibling()) {
            if (tokens.contains(currentElement.getNode().getElementType())) return true;
        }
        return false;
    }

    /**
     * Checks whether the current, previous or next comments matches the regex
     *
     * @param element          the element from which to start the search
     * @param regex            the regex that should be matched
     * @param doNotCountMyself if true, at least 2 occurrences need to be found instead of 1
     * @return true if the regex could be matched across the comments
     */
    public static boolean doLinkedCommentsContain(@NotNull PsiElement element, String regex, boolean doNotCountMyself) {
        PsiElement javaElement;
        if (element.getLanguage().equals(JavaLanguage.INSTANCE)) {
            javaElement = element instanceof PsiComment ? element.getParent() : element;
        } else {
            javaElement = getJavaContext(element);
        }
        PsiComment[] children = PsiTreeUtil.getChildrenOfType(javaElement, PsiComment.class);
        if (children == null || children.length == 0) return false;
        ArrayList<PsiComment> comments = new ArrayList<>(Arrays.asList(children));
        return countTextMatchesAcrossComments(comments, regex, (doNotCountMyself ? 2 : 1)) >= (doNotCountMyself ? 2 : 1);
    }

    /**
     * Counts the amount of matches with the regex across the comments in the list
     *
     * @param comments the list of comments to search in
     * @param regex    the regex that should be matched
     * @param maxCount how many matches should be found to stop the search sooner
     * @return the number of matches found
     */
    private static int countTextMatchesAcrossComments(@NotNull ArrayList<PsiComment> comments, String regex, int maxCount) {
        // only captures whole words by using negative lookahead
        Pattern pattern = Pattern.compile("(?<=@|;|\\*\\)|" + ALL_MODIFIERS_REGEX + ")\\s*(" + regex + ")(?!\\w)");
        int count = 0;
        for (PsiComment comment : comments) {
            String commentText = comment.getText();
            // check that it is a JML comment
            if (commentText.startsWith("/*@") || commentText.startsWith("//@")) {
                Matcher matcher = pattern.matcher(commentText);
                while (matcher.find()) {
                    count++;
                }
                if (count >= maxCount) return count;
            }
        }
        return count;
    }

    /**
     * Finds the first modifier that has a certain token type
     *
     * @param modifiers the list of modifiers
     * @param tokens    the tokens out of which one needs to match with the token-type of the modifier
     * @return a matching modifier, or null if it could not be found
     */
    public static PsiElement findFirstModifierInInvariant(JMLModifiers modifiers, TokenSet tokens) {
        if (modifiers == null) return null;
        for (PsiElement modifier = modifiers.getFirstChild(); modifier != null; modifier = modifier.getNextSibling()) {
            if (tokens.contains(modifier.getNode().getElementType())) return modifier;
        }
        return null;
    }

}
