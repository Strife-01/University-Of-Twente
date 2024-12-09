package nl.utwente.jmlplugin.lexer;

import com.intellij.lang.java.lexer.JavaLexer;
import com.intellij.lexer.LayeredLexer;
import com.intellij.pom.java.LanguageLevel;
import com.intellij.psi.tree.IElementType;
import nl.utwente.jmlplugin.psi.JMLTypes;

/**
 * Lexer that alternates between the JML and Java lexers dynamically to introduce Java tokens into the
 * JML token stream.
 */

public class JMLMultiLayerLexer extends LayeredLexer {

    IElementType[] javaStart = {JMLTypes.JAVA_EXPR_TOKEN};
    IElementType[] javaStop = {JMLTypes.SEMICOLON};

    public JMLMultiLayerLexer() {
        super(new JMLMergingLexer());
        LayeredLexer javaLexer = new LayeredLexer(new JavaLexer(LanguageLevel.HIGHEST));
        registerSelfStoppingLayer(javaLexer, javaStart, javaStop);
    }
}
