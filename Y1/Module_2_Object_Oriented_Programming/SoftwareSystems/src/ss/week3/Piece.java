package ss.week3;

public interface Piece {
    public boolean canMoveTo(int row, int column);
    public void moveTo(int row, int column);
    default public boolean availableSpot(int row, int column) {
        return (row >= 1 && row <= 8) && (column >= 1 && column <= 8);
    }
}
