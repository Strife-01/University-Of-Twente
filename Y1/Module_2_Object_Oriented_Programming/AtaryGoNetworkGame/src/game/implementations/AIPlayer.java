package game.implementations;

import game.ai.Strategy;
import game.interfaces.AbstractPlayer;
import game.interfaces.Game;
import game.interfaces.Move;
import game.utils.Stone;

public class AIPlayer extends AbstractPlayer {
    private Strategy strategy;

    public AIPlayer(Strategy strategy, Stone s) {
        this.strategy = strategy;
        super.name = strategy.getName();
        super.playerStone = s;
    }

    /**
     * @return the player stone
     */
    /*@ requires playerStone != null;
      @ ensures \result != null;
    */
    @Override
    public Stone getPlayerStone() {
        return this.playerStone;
    }

    /**
     * Determines the move for AIPlayer.
     * @param game current game
     * @return the move selected by AI
     */
    /*@ requires game != null;
      @ ensures \result != null;
    */
    @Override
    public Move determineMove(Game game) {
        return this.strategy.determineMove(game);
    }

    /**
     * @return the name of the AI player
     */
    /*@ ensures \result != null;
      @ ensures \result.equals(name);
    */
    @Override
    public String getName() {
        return this.name;
    }

    /**
     * Sets the name of the AI player.
     * @param name to set the AI player's name
     */
    /*@ requires name != null;
      @ ensures this.name.equals(name);
    */
    @Override
    public void setName(String name) {
        this.name = name;
    }
}

