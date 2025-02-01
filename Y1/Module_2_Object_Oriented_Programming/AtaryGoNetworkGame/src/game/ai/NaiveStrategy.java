package game.ai;

import game.implementations.GoGame;
import game.interfaces.Game;
import game.interfaces.Move;
import java.util.List;

/**
 * This class implements the {@link Strategy} interface and provides a simple, naive AI strategy.
 */
public class NaiveStrategy implements Strategy{

    /**
     * @return the name of this strategy ("Naive AI").
     */

    @Override
    public String getName() {
        return "Naive AI";
    }

    /**
     * @param game the current game state, used to retrieve valid moves.
     * @return a randomly selected valid {@link Move}.
     * @throws IllegalStateException if no valid moves are available.
     */
    //@ requires game != null;
    //@ ensures \result != null;
    //@ ensures game.getValidMoves().contains(\result);
    //@ pure
    @Override
    public Move determineMove(Game game) {
        return game.getValidMoves().get((int) (Math.random()*(game.getValidMoves().size())));
    }
}
