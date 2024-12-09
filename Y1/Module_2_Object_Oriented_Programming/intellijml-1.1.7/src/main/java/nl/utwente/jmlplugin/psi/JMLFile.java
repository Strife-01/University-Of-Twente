package nl.utwente.jmlplugin.psi;

import com.intellij.extapi.psi.PsiFileBase;
import com.intellij.openapi.fileTypes.FileType;
import com.intellij.psi.FileViewProvider;
import nl.utwente.jmlplugin.JMLFileType;
import nl.utwente.jmlplugin.JMLLanguage;
import org.jetbrains.annotations.NotNull;

/**
 * Class that represents the JML file as root
 */
public class JMLFile extends PsiFileBase {

    public JMLFile(@NotNull FileViewProvider viewProvider) {
        super(viewProvider, JMLLanguage.INSTANCE);
    }

    @Override
    public @NotNull FileType getFileType() {
        return JMLFileType.INSTANCE;
    }

    @Override
    public String toString() {
        return "JML File";
    }
}
