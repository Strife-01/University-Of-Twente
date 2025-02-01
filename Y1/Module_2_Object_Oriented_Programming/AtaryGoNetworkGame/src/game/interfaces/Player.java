package game.interfaces;

import game.utils.Stone;

/**
 * Marks objects as players. Each player has a stone, a name, and a method for determining their move
 * in a given game.
 */
public interface Player {

    /**
     * Returns the stone of the player (e.g., BLACK or WHITE).
     * @return the stone (Mark) of the player
     */
    /*@ ensures \result != null;
      @*/
    Stone getPlayerStone();

    /**
     * Determines the move for the player.
     * @param game the current game in which the move is being made
     * @return the move chosen by the player
     */
    /*@ requires game != null;
      @*/
    Move determineMove(Game game);

    /**
     * Returns the name of the player.
     * @return the name of the player
     */
    /*@ ensures \result != null && \result.length() > 0;
      @*/
    String getName();

    /**
     * Sets the name of the player.
     * @param name the name to set
     */
    /*@ requires name != null && name.length() > 0;
      @*/
    void setName(String name);
}

