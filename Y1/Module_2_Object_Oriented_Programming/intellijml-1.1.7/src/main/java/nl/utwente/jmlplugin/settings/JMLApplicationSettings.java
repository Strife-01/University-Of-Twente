package nl.utwente.jmlplugin.settings;

import com.intellij.openapi.components.PersistentStateComponent;
import com.intellij.openapi.components.ServiceManager;
import com.intellij.openapi.components.State;
import com.intellij.openapi.components.Storage;
import com.intellij.util.xmlb.XmlSerializerUtil;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

/**
 * Model part of the MVC pattern for the JML settings page. This is where the persistent storage of the plugin
 * settings is stored.
 */
@State(name = "JMLPluginSettings", storages = @Storage("other.xml"))
public class JMLApplicationSettings implements PersistentStateComponent<JMLApplicationSettings> {

    public boolean RUNTIME_CHECKING_ENABLED;
    public boolean RAINBOW_MODE;

    public JMLApplicationSettings() {
        RUNTIME_CHECKING_ENABLED = false;
        RAINBOW_MODE = false;
    }

    /**
     * Gets the instance of this class
     *
     * @return the instance of this class
     */
    public static JMLApplicationSettings getInstance() {
        return ServiceManager.getService(JMLApplicationSettings.class);
    }

    @Override
    public @Nullable JMLApplicationSettings getState() {
        return this;
    }

    @Override
    public void loadState(@NotNull JMLApplicationSettings state) {
        XmlSerializerUtil.copyBean(state, this);
    }
}
