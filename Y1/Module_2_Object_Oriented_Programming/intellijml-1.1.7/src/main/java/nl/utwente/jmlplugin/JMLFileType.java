package nl.utwente.jmlplugin;

import com.intellij.openapi.editor.colors.EditorColorsScheme;
import com.intellij.openapi.editor.highlighter.EditorHighlighter;
import com.intellij.openapi.fileTypes.EditorHighlighterProvider;
import com.intellij.openapi.fileTypes.FileType;
import com.intellij.openapi.fileTypes.FileTypeEditorHighlighterProviders;
import com.intellij.openapi.fileTypes.LanguageFileType;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.vfs.VirtualFile;
import nl.utwente.jmlplugin.syntax_highlighting.JMLEditorHighlighter;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import javax.swing.*;

/**
 * Class the represents the JML file type.
 * We do not implement JML templates, so this is mostly for internal testing purposes.
 */
public class JMLFileType extends LanguageFileType {

    public static final JMLFileType INSTANCE = new JMLFileType();

    // a nonsense string so that students don't get the bright idea to make .jml files
    public static final String DEFAULT_EXTENSION = "jukmifgguggh";

    private JMLFileType() {
        super(JMLLanguage.INSTANCE);

        //noinspection Convert2Lambda
        FileTypeEditorHighlighterProviders.INSTANCE.addExplicitExtension(this, new EditorHighlighterProvider() {
            @Override
            public EditorHighlighter getEditorHighlighter(@Nullable Project project, @NotNull FileType fileType,
                                                          @Nullable VirtualFile virtualFile,
                                                          @NotNull EditorColorsScheme colors) {
                return new JMLEditorHighlighter(project, virtualFile, colors);
            }
        });
    }

    @Override
    public @NonNls
    @NotNull String getName() {
        return "JML File";
    }

    @Override
    public @NotNull String getDescription() {
        return "JML specification file";
    }

    @Override
    public @NotNull String getDefaultExtension() {
        return DEFAULT_EXTENSION;
    }

    @Override
    public @Nullable Icon getIcon() {
        return JMLIcons.FILE;
    }

}
