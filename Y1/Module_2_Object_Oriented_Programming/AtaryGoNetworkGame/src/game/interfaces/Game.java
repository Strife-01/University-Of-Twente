package game.interfaces;

import java.util.List;

/**
 * Interface that defines the behavior of a Go game.
 * This interface allows interacting with the game by providing methods to check the turn,
 * validate moves, determine the winner, and more.
 */
public interface Game {

    /**
     * Returns the player whose turn it is.
     * @return the player object whose turn it is
     */
    /*@ ensures \result != null;
      @*/
    Player getTurn();

    /**
     * Returns a list of all valid moves that can be made by the current player.
     * @return a list of possible moves
     */
    /*@ ensures \result != null;
      @ ensures \result.size() >= 0;
      @*/
    List<Move> getValidMoves();

    /**
     * Checks if a given move is valid for the current game state.
     * @param move the move to be checked
     * @return true if the move is valid, false otherwise
     */
    /*@ ensures \result == (\exists Move m; getValidMoves().contains(m) && m == move);
      @*/
    boolean isValidMove(Move move);

    /**
     * Executes the given move and updates the game state accordingly.
     * @param move the move to be played
     */
    /*@ requires isValidMove(move);
      @ ensures !isGameover() || getTurn() != \old(getTurn());
      @*/
    void doMove(Move move);

    /**
     * Checks if the game is over.
     * @return true if the game is over, false otherwise
     */
    /*@
        pure
    */
    boolean isGameover();

    /**
     * Returns the player who won the game.
     * @return the winner of the game, or null if no winner
     */
    /*@ ensures \result != null ==> \result == getTurn();
      @*/
    Player getWinner();

    /**
     * Clears the game board and resets the game state.
     */
    void clearGameBoard();
}

