package game.implementations;

import game.utils.Stone;
import game.interfaces.AbstractPlayer;
import game.interfaces.Game;
import game.interfaces.Move;

/**
 * Represents a human player in the Go game.
 */
public class HumanPlayer extends AbstractPlayer {

    /**
     * Initializes a new HumanPlayer.
     * @param name the name of the player
     * @param s the stone (mark) for the player (Black or White)
     */
    /*@ ensures this.name == name;
      @ ensures this.playerStone == s;
      @*/
    public HumanPlayer(String name, Stone s) {
        super.name = name;
        super.playerStone = s;
    }

    /**
     * Returns the stone (mark) that the player is using.
     * @return the player's stone
     */
    /*@ ensures \result == this.playerStone;
      @*/
    @Override
    public synchronized Stone getPlayerStone() {
        return this.playerStone;
    }

    /**
     * Asks the human player for their move coordinates and validates the move.
     * @param game the current game instance
     * @return the move chosen by the player
     */
    /*@ ensures \result != null;
      @ ensures game.isValidMove(\result);
      @*/
    @Override
    public synchronized Move determineMove(Game game) {
        Move currentMove = null;
        while (true) {
            try {
                System.out.println("Please enter the coordinates for your move:");

                // Read row input
                System.out.print("row = ");
                String rowInput = ((GoGame) game).getGameScanner().nextLine();
                int i = Integer.parseInt(rowInput) - 1; // 0 indexed

                // Read column input
                System.out.print("column = ");
                String columnInput = ((GoGame) game).getGameScanner().nextLine();
                int j = Integer.parseInt(columnInput) - 1; // 0 indexed

                // Create a new move and validate it
                currentMove = new GoMove(i, j, this.playerStone);
                if (game.isValidMove(currentMove)) {
                    break; // Exit the loop if the move is valid
                } else {
                    System.out.println("Invalid move. Please enter valid coordinates.");
                }
            } catch (NumberFormatException e) {
                System.out.println("Invalid input. Please enter numeric values for row and column.");
            }
        }

        return currentMove;
    }


    /**
     * Returns the name of the player.
     * @return the name of the player
     */
    /*@ ensures \result == this.name;
      @*/
    @Override
    public synchronized String getName() {
        return this.name;
    }

    /**
     * Sets the name of the current player.
     * @param name the name to set
     */
    /*@ ensures this.name == name;
      @*/
    @Override
    public synchronized void setName(String name) {
        this.name = name;
    }
}

