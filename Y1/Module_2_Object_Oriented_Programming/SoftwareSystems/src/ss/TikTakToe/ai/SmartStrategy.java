package ss.TikTakToe.ai;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Objects;
import ss.TikTakToe.*;

public class SmartStrategy implements Strategy {
    private final String NAME = "Smart";

    /**
     * Returns the name of the strategy the AI is applying to determine the next move.
     *
     * @return name of strategy
     */
    @Override
    public String getName() {
        return NAME;
    }

    /**
     * Computes the next move based on the strategy and the current state of the game
     * and returns it.
     *
     * @param game current state of the game
     * @return next move or null if no moves are valid
     */
    @Override
    public Move determineMove(Game game) {
        if (game.isGameover()) {
            return null;
        }

        ComputerPlayer ai = (ComputerPlayer) game.getTurn();
        Mark currentPlayerMark = ai.getPlayerMark();
        TicTacToeGame gameCopy = deepCopy(game);
        List<Move> validMoves = gameCopy.getValidMoves();
        List<Move> finalMoves = new ArrayList<>();

        // Check for winning or blocking moves
        for (Move move : validMoves) {
            // Create a fresh copy of the game state for each move
            TicTacToeGame tempGameCopy = deepCopy(gameCopy);

            // Simulate the move
            tempGameCopy.doMove(move);

            // Check if this move makes the AI win
            if (Objects.equals(tempGameCopy.getWinner(), ai)) {
                return move;
            }

            // Check if this move allows the opponent to win
            if (!leadsToOpponentWin(tempGameCopy, ai)) {
                finalMoves.add(move);
            }
        }

        // If no specific strategy applies, pick a random move
        return finalMoves.isEmpty() ? null : validMoves.get(new Random().nextInt(validMoves.size()));
    }

    /**
     * Checks if the given state of the game allows the opponent to win in the next move.
     *
     * @param gameCopy a deep copy of the game state
     * @param ai the AI player
     * @return true if the opponent can win, false otherwise
     */
    private boolean leadsToOpponentWin(TicTacToeGame gameCopy, ComputerPlayer ai) {
        List<Move> opponentValidMoves = gameCopy.getValidMoves();

        for (Move potentialMove : opponentValidMoves) {
            TicTacToeGame potentialGameCopy = deepCopy(gameCopy);
            potentialGameCopy.doMove(potentialMove);

            // Check if the opponent wins after this move
            if (Objects.equals(potentialGameCopy.getWinner(), gameCopy.getTurn())) {
                return true;
            }
        }

        return false;
    }

    /**
     * Creates a deep copy of the current game state.
     *
     * @param game the original game instance
     * @return a deep copy of the game
     */
    private TicTacToeGame deepCopy(Game game) {
        TicTacToeGame ticTacToeGame = (TicTacToeGame) game;
        return new TicTacToeGame(
                ticTacToeGame.getBoard().deepCopy(),
                ticTacToeGame.getGameDimensions(),
                (AbstractPlayer) ticTacToeGame.getTurn(),
                ticTacToeGame.getPlayer1(),
                ticTacToeGame.getPlayer2()
        );
    }
}
