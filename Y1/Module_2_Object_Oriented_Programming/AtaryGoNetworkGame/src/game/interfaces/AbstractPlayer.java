package game.interfaces;

import game.utils.Stone;

/**
 * Represents an abstract player in the Go game.
 * This class contains the common attributes and methods for any type of player.
 * Concrete implementations must provide specific implementations for determining moves
 * and interacting with the game.
 */
public abstract class AbstractPlayer implements Player {
    /** The name of the player. */
    protected String name;

    /** The stone (mark) of the player (e.g., Black or White) */
    protected Stone playerStone;

    /**
     * Returns the stone (mark) that the player is using.
     * @return the player's stone
     */
    /*@ ensures \result == this.playerStone;
      @*/
    abstract public Stone getPlayerStone();

    /**
     * Determines the next move for the player.
     * This method must be implemented by subclasses to provide the logic for move selection.
     * @param game the current game instance
     * @return the move chosen by the player
     */
    /*@ ensures \result != null;
      @*/
    abstract public Move determineMove(Game game);

    /**
     * Returns the name of the player.
     * @return the name of the player
     */
    /*@ ensures \result == this.name;
      @*/
    abstract public String getName();

    /**
     * Sets the name of the player.
     * @param name the name to set
     */
    /*@ ensures this.name == name;
      @*/
    abstract public void setName(String name);
}

