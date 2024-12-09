package ss.TikTakToe.ui;

import java.util.Scanner;
import ss.TikTakToe.*;
import ss.TikTakToe.ai.NaiveStrategy;
import ss.TikTakToe.ai.SmartStrategy;

/**
 * Can start games and that asks the player whose turn it is to
 * determine their next move until the game is over.
 */
public class TicTacToeTUI {

    private Scanner sc;

    private void run() {
        sc = new Scanner(System.in);
        boolean playerWantsToPlay = true;

        while (playerWantsToPlay) {
            try {
                AbstractPlayer player1 = createPlayer(1, Mark.XX);
                AbstractPlayer player2 = createPlayer(2, Mark.OO);

                TicTacToeGame game = new TicTacToeGame(3, player1, player2);
                game.setGameScanner(sc);

                System.out.println("Welcome to the TicTacToe game!");

                while (!game.isGameover()) {
                    System.out.println(game.toString());
                    Player currentPlayer = game.getTurn();
                    Move move = (TicTacToeMove) ((AbstractPlayer) currentPlayer).determineMove(game);
                    game.doMove(move);
                }

                System.out.println(game.toString());
                if (game.getWinner() != null) {
                    System.out.println("Congratulations " + ((AbstractPlayer) game.getWinner()).getName() + ", you won!");
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

    private AbstractPlayer createPlayer(int playerNumber, Mark mark) {
        System.out.println("Select player " + playerNumber + " type:");
        System.out.println("1. Human");
        System.out.println("2. Naive AI");
        System.out.println("3. Smart AI");
        int choice = getValidChoice(1, 3);

        switch (choice) {
            case 1:
                System.out.print("Enter name for Player " + playerNumber + ": ");
                String name = sc.nextLine();
                return new HumanPlayer(name, mark);
            case 3:
                return new ComputerPlayer(new SmartStrategy(), mark);
            default:
                return new ComputerPlayer(new NaiveStrategy(), mark);
        }
    }

    private int getValidChoice(int min, int max) {
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

    private boolean askToPlayAgain(TicTacToeGame game) {
        System.out.print("Do you want another go? [y/n]: ");
        String answer = game.getGameScanner().nextLine();
        if (answer.equalsIgnoreCase("y")) {
            game.clearGameBoard();
            return true;
        }
        return false;
    }

    public static void main(String[] args) {
        TicTacToeTUI tui = new TicTacToeTUI();
        tui.run();
    }
}
