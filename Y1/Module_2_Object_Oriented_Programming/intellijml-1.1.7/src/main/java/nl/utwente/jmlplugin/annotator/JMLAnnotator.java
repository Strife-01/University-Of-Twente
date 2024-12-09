package nl.utwente.jmlplugin.annotator;

import com.intellij.codeInsight.highlighting.HighlightErrorFilter;
import com.intellij.lang.annotation.AnnotationHolder;
import com.intellij.lang.annotation.Annotator;
import com.intellij.lang.annotation.HighlightSeverity;
import com.intellij.openapi.application.ApplicationManager;
import com.intellij.openapi.editor.DefaultLanguageHighlighterColors;
import com.intellij.openapi.editor.colors.EditorColorsManager;
import com.intellij.openapi.editor.markup.TextAttributes;
import com.intellij.psi.PsiComment;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiErrorElement;
import com.intellij.psi.PsiWhiteSpace;
import com.intellij.psi.util.PsiTreeUtil;
import nl.utwente.jmlplugin.JMLLanguage;
import nl.utwente.jmlplugin.psi.JMLFile;
import nl.utwente.jmlplugin.psi.JMLJmlSpecification;
import nl.utwente.jmlplugin.psi.JMLTypes;
import org.jetbrains.annotations.NotNull;

import static com.intellij.psi.util.PsiTreeUtil.getChildOfType;
import static com.intellij.psi.util.PsiTreeUtil.getParentOfType;

/**
 * Does some general checking of the generated PSI Tree
 */
public class JMLAnnotator extends HighlightErrorFilter implements Annotator {
    @Override
    public void annotate(@NotNull PsiElement element, @NotNull AnnotationHolder holder) {
        // don't do any checking on whitespace or comments
        if (element instanceof PsiWhiteSpace || element instanceof PsiComment) return;

        // remove the green background that IntelliJ adds
        // disabled whilst unit testing, otherwise it is picked up as an annotation on every element by the tests
        if (element instanceof JMLFile && !ApplicationManager.getApplication().isUnitTestMode()) {
            TextAttributes textAttributes = new TextAttributes();
            textAttributes.setBackgroundColor(
                    EditorColorsManager.getInstance().getSchemeForCurrentUITheme().getDefaultBackground());
            holder.newSilentAnnotation(new HighlightSeverity("", 0)).enforcedTextAttributes(textAttributes).create();
        }

        // get the JML tree root
        JMLJmlSpecification jmlRoot;
        if (element instanceof JMLFile) {
            jmlRoot = getChildOfType(element, JMLJmlSpecification.class);
        } else if (element instanceof JMLJmlSpecification) {
            jmlRoot = (JMLJmlSpecification) element;
        } else {
            jmlRoot = getParentOfType(element, JMLJmlSpecification.class);
        }
        // if jmlRoot is null, then the element is probably enclosed by a PsiErrorElement
        if (jmlRoot == null) return;

        // check if there is whitespace between the start of the comment and the first @-sign,
        // if so, don't do any checking as it is not a JML comment
        if (jmlRoot.getPrevSibling() instanceof PsiWhiteSpace) {
            // set the foreground color to the default comment color, as it is not a JML comment
            // disabled whilst unit testing, otherwise it is picked up as an annotation on every element by the tests
            if (element instanceof JMLFile && !ApplicationManager.getApplication().isUnitTestMode()) {
                TextAttributes textAttributes = new TextAttributes();
                textAttributes.setForegroundColor(EditorColorsManager.getInstance().getSchemeForCurrentUITheme()
                        .getAttributes(DefaultLanguageHighlighterColors.BLOCK_COMMENT).getForegroundColor());
                holder.newSilentAnnotation(new HighlightSeverity("", 1)).enforcedTextAttributes(textAttributes).create();
            }
            // if the element itself is the first @-sign, then add a weak warning
            if (element.getNode().getElementType() == JMLTypes.AT_SIGN && jmlRoot.getFirstChild().equals(element)) {
                holder.newAnnotation(HighlightSeverity.WEAK_WARNING, ErrorMessages.WS_BEFORE_AT_SIGN).create();
            }
            return;
        }

        // do syntax checking
        if (!JMLSyntaxAnnotator.annotateSyntax(element, holder)) return;

        // skip other checkers when the tree contains errors
        if (PsiTreeUtil.findChildOfType(getParentOfType(element, JMLFile.class), PsiErrorElement.class) != null)
            return;

        // do semantic checking
        if (!JMLSemanticsAnnotator.annotateSemantics(element, jmlRoot, holder)) return;

        // do type checking
        JMLTypeAnnotator.annotateTypes(element, holder);
    }


    // makes sure that the parser does not display its errors, as we already do that in the annotators
    @Override
    public boolean shouldHighlightErrorElement(@NotNull PsiErrorElement element) {
        return element.getParent().getLanguage() != JMLLanguage.INSTANCE;
    }
}
