package ss.TikTakToe;

/**
 * Represents the move to place a specific mark on a specific place.
 */
public class TicTacToeMove implements Move {
    private final int rowIndex;
    private final int columnIndex;
    private final Mark mark;

    public TicTacToeMove(int rowIndex, int columnIndex, Mark mark) {
        this.rowIndex = rowIndex;
        this.columnIndex = columnIndex;
        this.mark = mark;
    }

    public int getRowIndex() {
        return rowIndex;
    }

    public int getColumnIndex() {
        return columnIndex;
    }

    public Mark getMark() {
        return mark;
    }
}
