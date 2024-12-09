package nl.utwente.jmlplugin.annotator;

import com.intellij.psi.PsiType;
import org.jetbrains.annotations.NotNull;

import java.util.HashMap;
import java.util.Map;

/**
 * Holder for all the variables that are manually kept track of during type checking
 */
class ExtraVariables {
    private final Map<String, PsiType> vars = new HashMap<>();

    public ExtraVariables() {

    }

    public ExtraVariables(ExtraVariables extraVars) {
        vars.putAll(extraVars.vars);
    }

    /**
     * Adds a new variable to the holder
     *
     * @param name the name of the variable
     * @param type the type of the variable
     */
    public void add(@NotNull String name, @NotNull PsiType type) {
        vars.put(name, type);
    }

    /**
     * Finds a variable by its name and returns the type of it
     *
     * @param name the name of the variable
     * @return the type of the found variable or null when the variable could not be found
     */
    public PsiType findVarAndGetType(@NotNull String name) {
        return vars.get(name);
    }

    /**
     * Checks that the holder contains a variable with a certain name
     *
     * @param name the name of the variable
     * @return true if the holder contains the variable
     */
    public boolean contains(@NotNull String name) {
        return vars.containsKey(name);
    }
}
