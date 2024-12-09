package nl.utwente.jmlplugin.syntax_highlighting;

import com.intellij.lang.java.JavaLanguage;
import com.intellij.lexer.Lexer;
import com.intellij.openapi.editor.DefaultLanguageHighlighterColors;
import com.intellij.openapi.editor.colors.TextAttributesKey;
import com.intellij.openapi.fileTypes.SyntaxHighlighter;
import com.intellij.openapi.fileTypes.SyntaxHighlighterBase;
import com.intellij.openapi.fileTypes.SyntaxHighlighterFactory;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.vfs.VirtualFile;
import com.intellij.psi.JavaTokenType;
import com.intellij.psi.tree.IElementType;
import nl.utwente.jmlplugin.lexer.JMLInJavaExprMergingLexer;
import nl.utwente.jmlplugin.psi.JMLTokenSet;
import nl.utwente.jmlplugin.psi.JMLTypes;
import org.jetbrains.annotations.NotNull;

import java.util.HashMap;
import java.util.Map;

import static com.intellij.openapi.editor.colors.TextAttributesKey.createTextAttributesKey;

/**
 * JML syntax highlighter class that defines the logic for the coloring of the
 * parse tree elements.
 */
public class JMLSyntaxHighlighter extends SyntaxHighlighterBase {

    private SyntaxHighlighter java;

    public JMLSyntaxHighlighter(Project project, VirtualFile virtualFile) {
        java = SyntaxHighlighterFactory.getSyntaxHighlighter(JavaLanguage.INSTANCE, project, virtualFile);
    }

    public JMLSyntaxHighlighter() {

    }

    //declarations of highlighter classes
    public static final TextAttributesKey KEY =
            createTextAttributesKey("JML_KEY", DefaultLanguageHighlighterColors.KEYWORD);
    public static final TextAttributesKey VISIBILITY_KEY =
            createTextAttributesKey("JML_VISIBILITY_KEY", DefaultLanguageHighlighterColors.KEYWORD);
    public static final TextAttributesKey BACKSLASH_KEY =
            createTextAttributesKey("JML_BACKSLASH_KEY", DefaultLanguageHighlighterColors.KEYWORD);
    public static final TextAttributesKey COMMENT =
            createTextAttributesKey("JML_COMMENT", DefaultLanguageHighlighterColors.BLOCK_COMMENT);
    public static final TextAttributesKey TEXT =
            createTextAttributesKey("JML_TEXT", DefaultLanguageHighlighterColors.BLOCK_COMMENT);
    public static final TextAttributesKey IDENTIFIER =
            createTextAttributesKey("JML_IDENTIFIER", DefaultLanguageHighlighterColors.IDENTIFIER);
    public static final TextAttributesKey GROUPING =
            createTextAttributesKey("JML_GROUPING", DefaultLanguageHighlighterColors.BRACKETS);
    public static final TextAttributesKey PUNCTUATION =
            createTextAttributesKey("JML_PUNCTUATION", DefaultLanguageHighlighterColors.BLOCK_COMMENT);
    public static final TextAttributesKey AT_SIGN =
            createTextAttributesKey("JML_AT_SIGN", DefaultLanguageHighlighterColors.DOC_COMMENT_TAG);


    //group highlighter classes together
    private static final TextAttributesKey[] DEFAULT = new TextAttributesKey[0];

    @Override
    public @NotNull Lexer getHighlightingLexer() {
        return new JMLInJavaExprMergingLexer();
    }

    private static final Map<IElementType, TextAttributesKey> tokensToTextAttributeKeys = new HashMap<>();

    static {
        // fill the map with JML tokens to their corresponding TextAttributesKey
        fillMap(tokensToTextAttributeKeys, JMLTokenSet.visibilityModifiers, VISIBILITY_KEY);
        fillMap(tokensToTextAttributeKeys, VISIBILITY_KEY, JMLTypes.STATIC, JMLTypes.INSTANCE);
        fillMap(tokensToTextAttributeKeys, JMLTokenSet.allOuterKeywords, KEY);
        fillMap(tokensToTextAttributeKeys, JMLTokenSet.backslashKeywords, BACKSLASH_KEY);
        fillMap(tokensToTextAttributeKeys, COMMENT, JMLTypes.INFORMAL_DESCRIPTION);
        fillMap(tokensToTextAttributeKeys, TEXT, JMLTypes.REST);
        fillMap(tokensToTextAttributeKeys, JMLTokenSet.punctuation, PUNCTUATION);
        fillMap(tokensToTextAttributeKeys, JMLTokenSet.grouping, GROUPING);
        fillMap(tokensToTextAttributeKeys, IDENTIFIER, JMLTypes.IDENT, JavaTokenType.IDENTIFIER, JMLTypes.STAR);
        fillMap(tokensToTextAttributeKeys, AT_SIGN, JMLTypes.AT_SIGN);
    }

    /**
     * Returns the type of highlighting that should be applied to the provided IElementType.
     *
     * @param tokenType - the element that needs to be provided the coloring type.
     * @return the coloring of the token.
     */
    @Override
    public TextAttributesKey @NotNull [] getTokenHighlights(IElementType tokenType) {
        // get TextAttributesKey for JML tokens
        if (tokensToTextAttributeKeys.containsKey(tokenType)) {
            return new TextAttributesKey[]{tokensToTextAttributeKeys.get(tokenType)};
        }
        // get TextAttributesKey for Java tokens
        if (this.java != null) {
            TextAttributesKey[] res = this.java.getTokenHighlights(jmlToJavaTokenType.getOrDefault(tokenType, tokenType));
            if (res.length != 0) return res;
        }
        return DEFAULT;
    }

    // THIS and SUPER need to be converted to their Java equivalents
    private static final Map<IElementType, IElementType> jmlToJavaTokenType = new HashMap<>();

    static {
        jmlToJavaTokenType.put(JMLTypes.THIS, JavaTokenType.THIS_KEYWORD);
        jmlToJavaTokenType.put(JMLTypes.SUPER, JavaTokenType.SUPER_KEYWORD);
    }
}
