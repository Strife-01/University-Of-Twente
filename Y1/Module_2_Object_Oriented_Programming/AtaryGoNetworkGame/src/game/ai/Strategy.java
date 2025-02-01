package game.ai;

import game.interfaces.Game;
import game.interfaces.Move;

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
        pure
    */
    public Move determineMove(Game game);
}

