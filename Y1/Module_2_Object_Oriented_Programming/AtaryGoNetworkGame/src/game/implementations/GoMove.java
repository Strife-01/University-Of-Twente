package game.implementations;

import game.utils.Stone;
import game.interfaces.Move;

/**
 * Represents a move in the game of Go where a specific mark is placed on a specific position of the board.
 */
public class GoMove implements Move {
    private final int rowIndex;
    private final int columnIndex;
    private final Stone s;

    /**
     * Initializes a new Go move.
     * @param rowIndex the row index where the move is to be made
     * @param columnIndex the column index where the move is to be made
     * @param s the stone (mark) being placed (Black or White)
     */
    /*@ ensures this.rowIndex == rowIndex;
      @ ensures this.columnIndex == columnIndex;
      @ ensures this.s == s;
      @*/
    public GoMove(int rowIndex, int columnIndex, Stone s) {
        this.rowIndex = rowIndex;
        this.columnIndex = columnIndex;
        this.s = s;
    }

    /**
     * Returns the row index where the move is made.
     * @return the row index
     */
    /*@ ensures \result == this.rowIndex;
      @*/
    public int getRowIndex() {
        return rowIndex;
    }

    /**
     * Returns the column index where the move is made.
     * @return the column index
     */
    /*@ ensures \result == this.columnIndex;
      @*/
    public int getColumnIndex() {
        return columnIndex;
    }

    /**
     * Returns the stone (mark) being placed on the board (Black or White).
     * @return the stone
     */
    /*@ ensures \result == this.s;
      @*/
    public Stone getMark() {
        return s;
    }
}

