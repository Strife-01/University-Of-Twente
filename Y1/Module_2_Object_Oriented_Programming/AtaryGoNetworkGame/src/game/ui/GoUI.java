package game.ui;

import game.interfaces.Game;
import game.interfaces.Player;
import game.utils.Stone;
import java.util.Scanner;

/**
 * Represents the user interface for the Capture Go game.
 * This interface defines methods to run the game, create players, validate choices,
 * and ask if the user wants to play again.
 */
public interface GoUI {

    /**
     * Starts the game loop, allowing players to make moves until the game ends.
     * The game continues until there is a winner or a tie.
     */
    void run();

    /**
     * Creates a player based on the specified player number and stone color.
     * This method allows for various types of players to be created (e.g., human or AI).
     *
     * @param playerNumber the number of the player (1 or 2)
     * @param s the stone color for the player (BLACK or WHITE)
     * @return the created player
     */
    Player createPlayer(int playerNumber, Stone s);

    /**
     * Prompts the user to enter a valid choice between the given minimum and maximum values.
     * Ensures that the input is a valid integer within the specified bounds.
     *
     * @param min the minimum valid choice
     * @param max the maximum valid choice
     * @return the valid choice made by the user
     * @throws IllegalArgumentException if the user input is not a valid integer within the range
     */
    int getValidChoice(int min, int max);

    /**
     * Asks the player if they would like to play again after a game has finished.
     *
     * @param game the current game instance
     * @return true if the player wants to play again, false otherwise
     */
    boolean askToPlayAgain(Game game);
}
