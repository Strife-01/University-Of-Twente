package nl.utwente.jmlplugin.settings;

import com.intellij.openapi.editor.colors.EditorColors;
import com.intellij.openapi.editor.colors.EditorColorsManager;

import javax.swing.*;
import java.awt.*;


/**
 * GUI view element of the MVC pattern for the JML options menu.
 */
public class ConfigurationPanel extends JPanel {

    private JCheckBox runtimeCheckingEnabled;
    private JCheckBox easterEggCheckbox;

    public ConfigurationPanel() {
        buildGUI();
    }

    /**
     * Generates the GUI elements for the settings page
     */
    private void buildGUI() {
        // runtime checking settings are not show as there is currently no fully functional runtime checking implementation
        runtimeCheckingEnabled = new JCheckBox("Enable runtime checking");
        runtimeCheckingEnabled.setToolTipText("Enable code injection at runtime to verify that" +
                " the JML specification is adhered to");
        easterEggCheckbox = new JCheckBox("???");
        easterEggCheckbox.setToolTipText("???");

        setLayout(new BorderLayout());

        JPanel topPane = new JPanel();
        topPane.setLayout(new BoxLayout(topPane, BoxLayout.Y_AXIS));
        topPane.add(easterEggCheckbox);

        add(topPane, BorderLayout.NORTH);
    }

    boolean isEasterEggEnabled() {
        return easterEggCheckbox.isSelected();
    }

    void setEasterEggEnabled(boolean enabled) {
        easterEggCheckbox.setSelected(enabled);
    }

    boolean isRuntimeCheckingEnabled() {
        return runtimeCheckingEnabled.isSelected();
    }

    void setRuntimeCheckingEnabled(boolean enabled) {
        runtimeCheckingEnabled.setSelected(enabled);
    }

}
