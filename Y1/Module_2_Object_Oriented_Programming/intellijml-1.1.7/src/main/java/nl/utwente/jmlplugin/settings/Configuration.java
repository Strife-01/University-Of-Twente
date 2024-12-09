package nl.utwente.jmlplugin.settings;

import com.intellij.openapi.options.BaseConfigurable;
import com.intellij.openapi.options.ConfigurationException;
import com.intellij.openapi.project.ProjectManager;
import com.intellij.openapi.project.ex.ProjectManagerEx;
import org.jetbrains.annotations.Nullable;

import javax.swing.*;

/**
 * Controller of the MVC pattern for the JML settings page.
 */
public class Configuration extends BaseConfigurable {
    private ConfigurationPanel panel;

    private final JMLApplicationSettings settings;

    public Configuration() {
        settings = JMLApplicationSettings.getInstance();
    }

    @Override
    public String getDisplayName() {
        return "IntelliJML";
    }

    @Override
    public @Nullable JComponent createComponent() {
        panel = new ConfigurationPanel();
        return panel;
    }

    /**
     * Check whether there are modified settings
     *
     * @return true is there are modified settings
     */
    @Override
    public boolean isModified() {
        return isRuntimeCheckingEnabled() ^ panel.isRuntimeCheckingEnabled()
                || isEasterEggEnabled() ^ panel.isEasterEggEnabled();
    }

    /**
     * Called when the user applies the JML settings, set the internal settings according to the settings page
     */
    @Override
    public void apply() throws ConfigurationException {
        settings.RAINBOW_MODE = panel.isEasterEggEnabled();
        settings.RUNTIME_CHECKING_ENABLED = panel.isRuntimeCheckingEnabled();
    }

    /**
     * Resets the settings page to the state of the internal settings
     */
    @Override
    public void reset() {
        panel.setRuntimeCheckingEnabled(isRuntimeCheckingEnabled());
        panel.setEasterEggEnabled(isEasterEggEnabled());
    }

    @Override
    public void disposeUIResources() {
        panel = null;
    }

    /**
     * Checks whether runtime checking is enabled in the internal settings
     *
     * @return true if runtime checking is enabled in the internal settings
     */
    private boolean isRuntimeCheckingEnabled() {
        return settings.RUNTIME_CHECKING_ENABLED;
    }

    private boolean isEasterEggEnabled() {
        return settings.RAINBOW_MODE;
    }

}
