package ss.TikTakToe;

public class HumanPlayer extends AbstractPlayer {
    public HumanPlayer(String name, Mark mark) {
        super.name = name;
        super.playerMark = mark;
    }

    /**
     * @return
     */
    @Override
    public Mark getPlayerMark() {
        return this.playerMark;
    }

    /**
     * Asks the player where to move.
     * @param game current game
     * @return move
     */

    @Override
    public Move determineMove(Game game) {
        Move currentMove = null;
        while (true) {
            try {
                System.out.println("Please enter the coordinates for your move:");

                // Read row input
                System.out.print("row = ");
                String rowInput = ((TicTacToeGame) game).getGameScanner().nextLine();
                int i = Integer.parseInt(rowInput) - 1; // 0 indexed

                // Read column input
                System.out.print("column = ");
                String columnInput = ((TicTacToeGame) game).getGameScanner().nextLine();
                int j = Integer.parseInt(columnInput) - 1; // 0 indexed

                // Create a new move and validate it
                currentMove = new TicTacToeMove(i, j, this.playerMark);
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
     * @return
     */
    @Override
    public String getName() {
        return this.name;
    }
}
