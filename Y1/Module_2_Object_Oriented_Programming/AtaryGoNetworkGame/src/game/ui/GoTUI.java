package game.ui;

import game.implementations.Board;
import game.implementations.GoGame;
import game.implementations.HumanPlayer;
import game.interfaces.Game;
import game.interfaces.Move;
import game.interfaces.Player;
import game.utils.Stone;
import java.util.Scanner;

/**
 * This class represents a text-based user interface for the Capture Go game.
 * It allows players to play a game of Capture Go through the command line.
 * The user can take turns with the AI or other human players, and the game continues until it is over.
 */
public class GoTUI implements GoUI {

    private Scanner sc;

    /**
     * Starts the game loop. The loop continues until the player decides to stop playing.
     * The method initializes the game, manages player turns, and displays the game status after each move.
     *
     * @throws RuntimeException if any runtime error occurs during gameplay.
     */
    /*@
      requires sc != null;
      @*/
    @Override
    public void run() {
        sc = new Scanner(System.in);
        boolean playerWantsToPlay = true;

        while (playerWantsToPlay) {
            try {
                Player player1 = createPlayer(1, Stone.BLACK);
                Player player2 = createPlayer(2, Stone.WHITE);

                GoGame game = new GoGame(Board.DIM, player1, player2);
                game.setGameScanner(sc);

                System.out.println("Welcome to the Capture Go game!");

                while (!game.isGameover()) {
                    System.out.println(game);
                    Player currentPlayer = game.getTurn();
                    Move move = currentPlayer.determineMove(game);
                    game.doMove(move);
                }

                System.out.println(game);
                if (game.getWinner() != null) {
                    System.out.println("Congratulations " + game.getWinner().getName() + ", you won!");
                } else {
                    System.out.println("It's a tie!");
                }

                playerWantsToPlay = askToPlayAgain(game);

            } catch (RuntimeException e) {
                e.printStackTrace();
            }
        }

        // Close System.in at the very end
        sc.close();
    }

    /**
     * Creates a player based on the player number and stone color.
     * This method asks the user to select a player type and provides a name for the player.
     *
     * @param playerNumber the number of the player (1 or 2)
     * @param s the stone color for the player (Black or White)
     * @return the newly created player
     * @throws IllegalArgumentException if an invalid player number or stone color is passed
     */
    /*@
      @requires playerNumber == 1 || playerNumber == 2;
      @requires s != null;
      @ensures \result != null;
      @ensures \result.getName() != null;
      */
    @Override
    public Player createPlayer(int playerNumber, Stone s) {
        System.out.println("Select player " + playerNumber + " type:");
        System.out.println("1. Human");
        //System.out.println("2. Naive AI");
        //System.out.println("3. Smart AI");
        int choice = getValidChoice(1, 3);
        String name = null;
        switch (choice) {
            // TODO: When we ask for a name check if the name is not already taken.
            case 1:
                System.out.print("Enter name for Player " + playerNumber + ": ");
                name = sc.nextLine();
                return new HumanPlayer(name, s);
            default:
                System.out.print("Only human players are allowed at the moment...\n" + "Enter name for Player " + playerNumber + ": ");
                name = sc.nextLine();
                return new HumanPlayer(name, s);
        }
    }

    /**
     * Prompts the user to select a valid choice within the given range.
     * Ensures that the input is a valid integer within the specified bounds.
     *
     * @param min the minimum valid choice
     * @param max the maximum valid choice
     * @return the valid choice made by the user
     * @throws IllegalArgumentException if the user input is not a valid integer within the range
     */
    /*@
     requires min <= max;
     ensures min <= \result && \result <= max;
     ensures \result != -1;
    @*/
    @Override
    public int getValidChoice(int min, int max) {
        int choice = -1;
        while (choice < min || choice > max) {
            try {
                System.out.print("Enter your choice (" + min + "-" + max + "): ");
                choice = Integer.parseInt(sc.nextLine());
            } catch (NumberFormatException e) {
                System.out.println("Invalid input. Please enter a number.");
            }
        }
        return choice;
    }

    /**
     * Asks the player if they want to play again after the game ends.
     *
     * @param game the current game instance
     * @return true if the player wants to play again, false otherwise
     */
    /*@
      requires game != null;
      ensures \result == true || \result == false;
      ensures game.isGameover();
      @*/
    @Override
    public boolean askToPlayAgain(Game game) {
        System.out.print("Do you want another go? [y/n]: ");
        String answer = ((GoGame) game).getGameScanner().nextLine();
        if (answer.equalsIgnoreCase("y")) {
            game.clearGameBoard();
            return true;
        }
        return false;
    }

    /**
     * Main method to run the GoTUI application.
     * It initializes the GoTUI and starts the game loop.
     *
     * @param args command-line arguments (not used in this implementation)
     */
    public static void main(String[] args) {
        GoTUI tui = new GoTUI();
        tui.run();
    }
}

