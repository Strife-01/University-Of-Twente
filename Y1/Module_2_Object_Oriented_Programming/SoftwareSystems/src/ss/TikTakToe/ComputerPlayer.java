package ss.TikTakToe;

import java.util.Map;
import ss.TikTakToe.ai.Strategy;

public class ComputerPlayer extends AbstractPlayer {
    private Strategy strategy;

    public ComputerPlayer(Strategy strategy, Mark mark) {
        this.strategy = strategy;
        super.playerMark = mark;
        super.name = strategy.getName() + "-" + super.playerMark;
    }

    /**
     * @return playerMark
     */
    @Override
    public Mark getPlayerMark() {
        return super.playerMark;
    }

    /**
     * @param game the state of the current game
     * @return The move according to the current strategy
     */
    @Override
    public Move determineMove(Game game) {
        return strategy.determineMove(game);
    }

    /**
     * @return the name of the computer player
     */
    @Override
    public String getName() {
        return super.name;
    }

    /**
     * Makes the current strategy available to the outside world.
     * @return current strategy
     */
    public Strategy getStrategy() {
        return this.strategy;
    }

    /**
     * Allows for change of strategy at runtime.
     * @param newStrategy the new strategy
     */
    public void setStrategy(Strategy newStrategy) {
        this.strategy = newStrategy;
    }
}
