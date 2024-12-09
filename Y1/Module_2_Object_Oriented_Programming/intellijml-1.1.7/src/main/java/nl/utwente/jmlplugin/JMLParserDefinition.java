package nl.utwente.jmlplugin;

import com.intellij.lang.ASTNode;
import com.intellij.lang.ParserDefinition;
import com.intellij.lang.PsiParser;
import com.intellij.lexer.Lexer;
import com.intellij.openapi.project.Project;
import com.intellij.psi.FileViewProvider;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiFile;
import com.intellij.psi.TokenType;
import com.intellij.psi.tree.IFileElementType;
import com.intellij.psi.tree.TokenSet;
import nl.utwente.jmlplugin.lexer.JMLInJavaExprMergingLexer;
import nl.utwente.jmlplugin.parser.JMLParser;
import nl.utwente.jmlplugin.psi.JMLFile;
import nl.utwente.jmlplugin.psi.JMLTypes;
import org.jetbrains.annotations.NotNull;

/**
 * Class that defines parser behaviour for the JML parser implementation.
 */
public class JMLParserDefinition implements ParserDefinition {

    public static final TokenSet WHITE_SPACES = TokenSet.create(TokenType.WHITE_SPACE);

    public static final TokenSet COMMENTS = TokenSet.create(JMLTypes.INFORMAL_DESCRIPTION);

    public static final IFileElementType FILE = new IFileElementType(JMLLanguage.INSTANCE);

    @Override
    public @NotNull Lexer createLexer(Project project) {
        return new JMLInJavaExprMergingLexer();
    }

    /**
     * Defines which characters are interpreted as white space by the parser
     *
     * @return set of whitespace tokens
     */

    @Override
    public @NotNull TokenSet getWhitespaceTokens() {
        return WHITE_SPACES;
    }

    @Override
    public @NotNull PsiParser createParser(final Project project) {
        return new JMLParser();
    }

    @Override
    public @NotNull IFileElementType getFileNodeType() {
        return FILE;
    }

    @Override
    public @NotNull TokenSet getCommentTokens() {
        return COMMENTS;
    }

    @Override
    public @NotNull TokenSet getStringLiteralElements() {
        return TokenSet.EMPTY;
    }

    @Override
    public @NotNull PsiElement createElement(ASTNode node) {
        return JMLTypes.Factory.createElement(node);
    }

    @Override
    public @NotNull PsiFile createFile(@NotNull FileViewProvider viewProvider) {
        return new JMLFile(viewProvider);
    }

    /**
     * Indicates whether a or not whitespace token is needed in between certain token types,
     * set to maybe to allow flexibility.
     *
     * @param left  - left ast node
     * @param right - right ast node
     * @return whether or not a whitespace is required between two tokens of the language.
     */

    @Override
    public @NotNull SpaceRequirements spaceExistenceTypeBetweenTokens(ASTNode left, ASTNode right) {
        return SpaceRequirements.MAY;
    }
}
