package game.interfaces;

import game.utils.Stone;

/**
 * Purpose to mark objects as Moves. The actual implementation is game-specific and will define
 * how a move is represented (e.g., coordinates, mark, etc.).
 */
public interface Move {
    /**
     * Returns the row index where the move is placed.
     * @return the row index of the move
     */
    /*@ ensures \result >= 0;
      @*/
    int getRowIndex();

    /**
     * Returns the column index where the move is placed.
     * @return the column index of the move
     */
    /*@ ensures \result >= 0;
      @*/
    int getColumnIndex();

    /**
     * Returns the mark (Stone) associated with the move (e.g., BLACK or WHITE).
     * @return the mark (Stone) of the move
     */
    /*@ ensures \result != null;
      @*/
    Stone getMark();
}

