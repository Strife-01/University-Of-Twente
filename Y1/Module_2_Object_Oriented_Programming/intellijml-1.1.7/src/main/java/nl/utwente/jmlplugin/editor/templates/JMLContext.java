package nl.utwente.jmlplugin.editor.templates;

import com.intellij.codeInsight.template.TemplateContextType;
import com.intellij.psi.PsiFile;
import nl.utwente.jmlplugin.JMLLanguage;
import org.jetbrains.annotations.NotNull;

/**
 * Provides a context definition for JML templates. The context here simply means where the template can be completed in.
 */

public class JMLContext extends TemplateContextType {
    protected JMLContext() {
        super("JML", "JML");
    }

    @Override
    @SuppressWarnings("deprecation") // Needed for compatibility with older versions of IntelliJ
    public boolean isInContext(@NotNull PsiFile file, int offset) {
        return file.getLanguage() == JMLLanguage.INSTANCE;
    }

}
