package nl.utwente.jmlplugin.completion;

/**
 * Enum for providing completion priority weights by which to order completion suggestions when they are displayed.
 */

public enum JMLCompletionWeights {
    STATIC_IMPORT_METHOD(1),
    STATIC_IMPORT_FIELD(2),
    LOCAL_METHOD(3),
    LOCAL_FIELD(4),
    KEYWORD(5);

    private final double weight;

    private JMLCompletionWeights(double weight) {
        this.weight = weight;
    }

    public double getWeight() {
        return weight;
    }
}
