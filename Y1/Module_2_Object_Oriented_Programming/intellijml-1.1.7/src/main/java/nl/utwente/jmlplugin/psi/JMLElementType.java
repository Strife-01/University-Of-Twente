package nl.utwente.jmlplugin.psi;

import com.intellij.psi.tree.IElementType;
import nl.utwente.jmlplugin.JMLLanguage;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;

/**
 * AST node type that specifies that the node is part of the JML language.
 */
public class JMLElementType extends IElementType {

    public JMLElementType(@NonNls @NotNull String debugName) {
        super(debugName, JMLLanguage.INSTANCE);
    }

}
