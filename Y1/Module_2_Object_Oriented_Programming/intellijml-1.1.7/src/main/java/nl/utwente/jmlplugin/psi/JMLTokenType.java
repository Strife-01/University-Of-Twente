package nl.utwente.jmlplugin.psi;

import com.intellij.psi.tree.IElementType;
import nl.utwente.jmlplugin.JMLLanguage;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;

/**
 * JML language token type class
 */
public class JMLTokenType extends IElementType {

    public JMLTokenType(@NonNls @NotNull String debugName) {
        super(debugName, JMLLanguage.INSTANCE);
    }

    @Override
    public String toString() {
        return super.toString();
    }


}
