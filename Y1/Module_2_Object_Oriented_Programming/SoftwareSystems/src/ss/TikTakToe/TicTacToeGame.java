package ss.TikTakToe;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

/**
 * Uses Mark and Board for the actual game representation.
 */
public class TicTacToeGame implements Game {
    private Board board;
    private int boardDimension;
    private AbstractPlayer turn;
    private AbstractPlayer player1;
    private AbstractPlayer player2;
    private Scanner gameScanner;

    public TicTacToeGame(int dimension, AbstractPlayer player1, AbstractPlayer player2) {
        board = new Board(dimension);
        turn = player1;
        this.player1 = player1;
        this.player2 = player2;
        boardDimension = dimension;
    }

    public TicTacToeGame(AbstractPlayer player1, AbstractPlayer player2) {
        this(3, player1, player2);
    }

    // Only for deep copy purposes
    public TicTacToeGame(Board board, int boardDimension, AbstractPlayer turn, AbstractPlayer player1, AbstractPlayer player2) {
        this(3, player1, player2);
        this.board = board;
        this.turn = turn;
    }

    /**
     * Returns the player whose turn is.
     * @return player object
     */
    @Override
    public Player getTurn() {
        return turn;
    }

    /**
     * Returns a list of all possible moves.
     * @return list of moves
     */
    @Override
    public List<Move> getValidMoves() {
        List<Move> legalMoves = new ArrayList<>();
        if (isGameover()) {
            return legalMoves;
        }
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                if (board.isEmptyField(i, j)) {
                    TicTacToeMove move = new TicTacToeMove(i, j, turn.getPlayerMark());
                    legalMoves.add(move);
                }
            }
        }
        return legalMoves;
    }

    /**
     * Checks if a move is a legal move.
     *
     * @param move to be checked
     * @return true if valid move
     */
    @Override
    public boolean isValidMove(Move move) {
        if (isGameover() || ((TicTacToeMove) move).getMark() != turn.getPlayerMark()) {
            return false;
        }
        int rowIndex = ((TicTacToeMove) move).getRowIndex();
        int columnIndex = ((TicTacToeMove) move).getColumnIndex();
        return board.isEmptyField(rowIndex, columnIndex);
    }

    /**
     * Plays the move provided as argument.
     *
     * @param move to be played
     */
    @Override
    public void doMove(Move move) {
        int rowIndex = ((TicTacToeMove) move).getRowIndex();
        int columnIndex = ((TicTacToeMove) move).getColumnIndex();
        board.setField(rowIndex, columnIndex, turn.getPlayerMark());
        if (turn == player1) {
            turn = player2;
        } else {
            turn = player1;
        }
    }

    /**
     * Checks if the game is over.
     *
     * @return true if the game is finished
     */
    @Override
    public boolean isGameover() {
        return board.gameOver();
    }

    public void clearGameBoard() {
        board.reset();
    }

    /**
     * Returns the player who won the match.
     *
     * @return winner of Player type
     */
    @Override
    public Player getWinner() {
        return board.isWinner(player1.getPlayerMark()) ? player1 : board.isWinner(player2.getPlayerMark()) ? player2 : null;
    }

    @Override
    public String toString() {
        StringBuilder boardString = new StringBuilder();
        int boardDimension = this.boardDimension;

        // Loop through rows
        for (int i = 0; i < boardDimension * 2 - 1; i++) {
            for (int j = 0; j < boardDimension * 2 - 1; j++) {
                if (i % 2 == 0) {
                    if (j % 2 == 0) {
                        // Print index or cell content for even rows/columns
                        boardString.append(" " + board.getField(i/2, j/2).toString() + " ");
                    } else {
                        // Column separator
                        boardString.append("|");
                    }
                } else { // Separator row
                    if (j % 2 == 0) {
                        // Row separator
                        boardString.append("---");
                    } else {
                        // Intersection
                        boardString.append("+");
                    }
                }
            }
            boardString.append("\n"); // Move to the next row
        }
        return "\n\nIt is " + turn.getName() + "'s turn.\n\n" + boardString.toString();
    }

    public Scanner getGameScanner() {
        return gameScanner;
    }

    public void setGameScanner(Scanner gameScanner) {
        this.gameScanner = gameScanner;
    }

    public void closeGameScanner() {
        gameScanner.close();
    }

    public int getGameDimensions() { return this.boardDimension; }

    public Board getBoard() { return this.board; }

    public AbstractPlayer getPlayer1() {
        return this.player1;
    }

    public AbstractPlayer getPlayer2() {
        return this.player2;
    }
}
