package ss.TikTakToe.ai;

import java.util.Random;
import ss.TikTakToe.*;

public class NaiveStrategy implements Strategy {
    private final String NAME = "Naive";
    /*@
        private invariant NAME == "Naive";
    */

    /**
     * Returns the name of the strategy the AI is applying to determine the next move.
     * @return name of strategy
     */
    @Override
    public String getName() {
        return this.NAME;
    }

    /**
     * Computes the next move based on the strategy and the current state of the game
     * and returns it.
     *
     * @param game current state of the game
     * @return next move or null
     */
    @Override
    public Move determineMove(Game game) {
        Random random = new Random();
        if (game.isGameover()) {
            return null;
        }
        int dimensions = ((TicTacToeGame) game).getGameDimensions();
        while (true) {
            Mark currentPlayerMark = ((ComputerPlayer) game.getTurn()).getPlayerMark();
            Move move = new TicTacToeMove(
                    random.nextInt(dimensions),
                    random.nextInt(dimensions),
                    currentPlayerMark
            );
            if (game.isValidMove(move)) {
                return move;
            }
        }
    }
}
