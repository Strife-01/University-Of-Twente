package ss.TikTakToe;

/**
 * Represents the X and O marks for the board.
 */
public enum Mark {
    EMPTY(" "),
    XX("X"),
    OO("O");

    private String description;

    Mark(String description) {
        this.description = description;
    }

    @Override
    public String toString() {
        return this.description;
    }
}
