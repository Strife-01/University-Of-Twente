package nl.utwente.jmlplugin;

import com.intellij.lang.InjectableLanguage;
import com.intellij.lang.Language;
import com.intellij.psi.templateLanguages.TemplateLanguage;
import org.jetbrains.annotations.NotNull;

/**
 * Class that represents the JML language in IntelliJ
 */
public class JMLLanguage extends Language implements TemplateLanguage, InjectableLanguage {

    public static final JMLLanguage INSTANCE = new JMLLanguage();

    private JMLLanguage() {
        super("JML");
    }

    @Override
    public @NotNull String getDisplayName() {
        return "JML";
    }

    @Override
    public boolean isCaseSensitive() {
        return true;
    }

}