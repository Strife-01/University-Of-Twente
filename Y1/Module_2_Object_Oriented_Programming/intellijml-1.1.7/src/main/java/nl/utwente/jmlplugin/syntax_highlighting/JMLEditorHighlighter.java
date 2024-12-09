package nl.utwente.jmlplugin.syntax_highlighting;

import com.intellij.lang.java.JavaLanguage;
import com.intellij.lexer.Lexer;
import com.intellij.openapi.editor.colors.EditorColorsScheme;
import com.intellij.openapi.editor.colors.TextAttributesKey;
import com.intellij.openapi.editor.ex.util.LayerDescriptor;
import com.intellij.openapi.editor.ex.util.LayeredLexerEditorHighlighter;
import com.intellij.openapi.fileTypes.SyntaxHighlighter;
import com.intellij.openapi.fileTypes.SyntaxHighlighterFactory;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.vfs.VirtualFile;
import com.intellij.psi.tree.IElementType;
import nl.utwente.jmlplugin.lexer.JMLInJavaExprMergingLexer;
import nl.utwente.jmlplugin.psi.JMLTypes;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

/**
 * This highlighter provides highlighting in embedded JML instances (Also tries to do some Java highlighting).
 */
public class JMLEditorHighlighter extends LayeredLexerEditorHighlighter {

    public JMLEditorHighlighter(@Nullable Project project, @Nullable VirtualFile virtualFile,
                                @NotNull EditorColorsScheme colors) {
        super(new JMLSyntaxHighlighter(project, virtualFile) {
            @Override
            public @NotNull Lexer getHighlightingLexer() {
                return new JMLInJavaExprMergingLexer();
            }
        }, colors);

        final SyntaxHighlighter java = SyntaxHighlighterFactory.getSyntaxHighlighter(JavaLanguage.INSTANCE,
                project, virtualFile);

        this.registerLayer(JMLTypes.JAVA_EXPR_TOKEN, new LayerDescriptor(new SyntaxHighlighter() {
            @Override
            public @NotNull Lexer getHighlightingLexer() {
                return java.getHighlightingLexer();
            }

            @Override
            public TextAttributesKey @NotNull [] getTokenHighlights(IElementType tokenType) {
                return java.getTokenHighlights(tokenType);
            }
        }, ""));
    }


}
