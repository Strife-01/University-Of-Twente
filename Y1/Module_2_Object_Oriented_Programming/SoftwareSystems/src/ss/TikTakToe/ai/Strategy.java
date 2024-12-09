package ss.TikTakToe.ai;

import ss.TikTakToe.Game;
import ss.TikTakToe.Move;

/**
 * The Strategy tells the AI in which way to determine the next move.
 */
public interface Strategy {
    /**
     * Returns the name of the strategy the AI is applying to determine the next move.
     * @return name of strategy
     */
    /*@
        ensures \result != null;
        pure
    */
    public String getName();

    /**
     * Computes the next move based on the strategy and the current state of the game
     * and returns it.
     * @param game current state of the game
     * @return next move or null
     */
    /*@
        requires game != null;
        requires game.isGameover() == false;
        ensures game.isGameover() == false ==> \result != null;
        ensures game.isGameover() == true ==> \result == null;
        pure
    */
    public Move determineMove(Game game);
}
