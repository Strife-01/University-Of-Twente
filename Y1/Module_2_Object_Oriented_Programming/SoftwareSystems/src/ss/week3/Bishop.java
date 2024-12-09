package ss.week3;

public class Bishop implements Piece {
    private int row;
    private int column;

    public Bishop(int row, int column) {
        if ((row < 1 || row > 8) || (column < 1 || column > 8)) {
            throw new RuntimeException("Invalid position");
        }

        this.row = row;
        this.column = column;
    }

    /**
     * @param row
     * @param column
     * @return
     */
    @Override
    public boolean canMoveTo(int row, int column) {
        return !(this.column == column && this.row == row) &&
                availableSpot(row, column) &&
                (Math.abs(this.row - row) == Math.abs(this.column - column));
    }

    /**
     * @param row
     * @param column
     */
    @Override
    public void moveTo(int row, int column) {
        if (canMoveTo(row, column)) {
            this.row = row;
            this.column = column;
        }
    }
}
