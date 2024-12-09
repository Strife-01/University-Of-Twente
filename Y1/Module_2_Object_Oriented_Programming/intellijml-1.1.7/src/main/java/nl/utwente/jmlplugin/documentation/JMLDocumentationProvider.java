package nl.utwente.jmlplugin.documentation;

import com.intellij.lang.java.JavaDocumentationProvider;
import com.intellij.openapi.editor.colors.TextAttributesKey;
import com.intellij.openapi.editor.markup.TextAttributes;
import com.intellij.psi.PsiComment;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiMethod;
import com.intellij.psi.tree.IElementType;
import nl.utwente.jmlplugin.lexer.JMLMultiLayerLexer;
import nl.utwente.jmlplugin.syntax_highlighting.JMLSyntaxHighlighter;
import org.jetbrains.annotations.Nls;
import java.awt.*;


/**
 * Class extending the Java documentation provider with extra functionality
 * to include JML statements in the quick documentation of Java methods.
 */

public class JMLDocumentationProvider extends JavaDocumentationProvider {

    // TODO Unit tests
    @Override
    public @Nls String generateDoc(PsiElement element, PsiElement originalElement) {
        // Original method return
        final String original = super.generateDoc(element, originalElement);


        // only add JML docs for methods
        if (element instanceof PsiMethod) {
            // search for the JML comment
            boolean jmlFound = false;
            StringBuilder resultBuilder = new StringBuilder(original == null ? "" : original);
            for (PsiElement elem: element.getChildren()) {
                if (elem instanceof PsiComment &&
                        (elem.getText().startsWith("/*@") || elem.getText().startsWith("//@"))) {

                    PsiComment jmlComment = (PsiComment) elem;

                    if (!jmlFound) {
                        // only add this once
                        resultBuilder.append("<div class='sections' style=\"max-width:100%;\"><div class='section' style=\"border-top:1px solid #595959; margin-top:5px; padding-top:3px\"/>" +
                                "<i>JML</i><span>&nbsp; annotations:</span>");
                        jmlFound = true;
                    }

                    // Get a lexer to get the token types in the comment
                    JMLSyntaxHighlighter syntaxHighlighter = new JMLSyntaxHighlighter();
                    JMLMultiLayerLexer lexer = new JMLMultiLayerLexer();
                    // remove the start of the comment
                    String jmlText = "\n"+jmlComment.getText().replaceAll("(//|/\\*|\\*/)","").trim();

                    // go through all tokens
                    lexer.start(jmlText);
                    while(lexer.getCurrentPosition().getOffset() < jmlText.length()) {
                        IElementType type = lexer.getTokenType();
                        if (type == null) break;
                        TextAttributesKey[] arr = syntaxHighlighter.getTokenHighlights(type);
                        if (arr.length > 0) {
                            // get the first, as that is usually the JML highlighting
                            TextAttributes attrs = arr[0].getDefaultAttributes();
                            // add foreground color and optional font-weight
                            Color fg = attrs.getForegroundColor();
                            resultBuilder.append("<span style=\"color:#").append(Integer.toHexString(fg.getRGB()).substring(2)).append(";");
                            if (attrs.getFontType() == Font.BOLD) resultBuilder.append("font-weight:bold;");
                            resultBuilder. append("\">").append(lexer.getTokenText()).append("</span>");
                        } else if (lexer.getTokenText().length() == 0) {
                            // don't add span around empty tokens
                            resultBuilder.append(lexer.getTokenText());
                        } else {
                            // no highlighting found, so just add the text itself,
                            // but do newlines with HTML newlines
                            String text = lexer.getTokenText().replaceAll("\n[ \t\r]*","<br/>");
                            resultBuilder.append("<span>").append(text).append("</span>");
                        }

                        lexer.advance();
                    }
                }
            }

            if (jmlFound) {
                resultBuilder.append("</div></div>");
                return resultBuilder.toString();
            }
        }

        return original;
    }
}
