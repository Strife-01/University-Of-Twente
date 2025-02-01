package game.utils;

/**
 * Represents the different types of stones (markers) that can be placed on a Go board.
 * The possible values are EMPTY, BLACK, and WHITE, each represented by a string value.
 * <p>
 * The enum is used to differentiate between empty spaces and the two possible stone colors
 * (Black and White) in a Go game.
 * </p>
 */
public enum Stone {

    /**
     * Represents an empty space on the board.
     */
    EMPTY(" "),

    /**
     * Represents a black stone on the board.
     */
    BLACK("B"),

    /**
     * Represents a white stone on the board.
     */
    WHITE("W");

    private String value;

    /**
     * Constructs a Stone with the specified string value.
     *
     * @param value the string value representing the stone
     */
    Stone(String value) {
        this.value = value;
    }

    /**
     * Returns the string representation of the stone.
     *
     * @return the string value of the stone
     */
    @Override
    public String toString() {
        return String.valueOf(this.value);
    }
}

