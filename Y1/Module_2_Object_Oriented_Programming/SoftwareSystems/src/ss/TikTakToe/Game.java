package ss.TikTakToe;

import java.util.List;

public interface Game {
    /**
     * Returns the player whose turn is.
     * @return player object
     */
    public Player getTurn();

    /**
     * Returns a list of all possible moves.
     * @return list of moves
     */
    public List<Move> getValidMoves();

    /**
     * Checks if a move is a legal move.
     * @param move to be checked
     * @return true if valid move
     */
    public boolean isValidMove(Move move);

    /**
     * Plays the move provided as argument.
     * @param move to be played
     */
    public void doMove(Move move);

    /**
     * Checks if the game is over.
     * @return true if the game is finished
     */
    /*@
        pure
    */
    public boolean isGameover();

    /**
     * Returns the player who won the match.
     * @return winner of Player type
     */
    public Player getWinner();

}
