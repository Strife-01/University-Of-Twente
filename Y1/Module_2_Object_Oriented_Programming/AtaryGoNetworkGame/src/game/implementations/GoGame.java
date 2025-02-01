package game.implementations;

import game.interfaces.Game;
import game.interfaces.Move;
import game.interfaces.Player;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

/**
 * Represents a Go game. Manages the game state, player turns, valid moves, and game logic.
 */
public class GoGame implements Game {
    private Board board;
    private final int boardDimension;
    private Player turn;
    private final Player player1;
    private final Player player2;
    private Scanner gameScanner;

    // The Black Stone Starts
    /**
     * Initializes a Go game with a specified board dimension and players.
     * @param dimension the dimension of the board (e.g., 7, 19)
     * @param player1 the first player
     * @param player2 the second player
     */
    /*@ ensures this.board != null;
      @ ensures this.turn == player1;
      @*/
    public GoGame(int dimension, Player player1, Player player2) {
        this.board = new Board(dimension);
        this.turn = player1;
        this.player1 = player1;
        this.player2 = player2;
        this.boardDimension = dimension;
    }

    /**
     * Initializes a Go game with a default board dimension of 7 and the specified players.
     * @param player1 the first player
     * @param player2 the second player
     */
    /*@ ensures this.board != null;
      @ ensures this.turn == player1;
      @*/
    public GoGame(Player player1, Player player2) {
        this(Board.DIM, player1, player2);
    }

    /**
     * Deep copy constructor for GoGame.
     * @param board the game board
     * @param boardDimension the board dimension
     * @param turn the current player's turn
     * @param player1 the first player
     * @param player2 the second player
     */
    /*@ ensures this.board != null;
      @ ensures this.turn == turn;
      @ ensures this.player1 == player1;
      @ ensures this.player2 == player2;
      @*/
    public GoGame(Board board, int boardDimension, Player turn, Player player1, Player player2) {
        this(boardDimension, player1, player2);
        this.board = board;
        this.turn = turn;
    }

    /**
     * Returns the player whose turn it is.
     * @return the player whose turn it is
     */
    /*@ ensures \result != null;
      @ ensures \result == turn;
      @*/
    @Override
    public synchronized Player getTurn() {
        return turn;
    }

    /**
     * Returns a list of all valid moves for the current game state.
     * @return list of valid moves
     */
    /*@ ensures \result != null;
      @ ensures (\forall Move m; \result.contains(m) ==> isValidMove(m));
      @*/
    @Override
    public synchronized List<Move> getValidMoves() {
        List<Move> legalMoves = new ArrayList<>();
        if (isGameover()) {
            return null;
        }
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                if (board.isEmptyField(i, j)) {
                    Move move = new GoMove(i, j, turn.getPlayerStone());
                    legalMoves.add(move);
                }
            }
        }
        return legalMoves;
    }

    /**
     * Checks if a move is valid.
     * @param move the move to be checked
     * @return true if the move is valid, false otherwise
     */
    /*@ ensures \result == (isGameover() == false && move.getMark() == turn.getPlayerStone() && board.isEmptyField(move.getRowIndex(), move.getColumnIndex()));
      @*/
    @Override
    public synchronized boolean isValidMove(Move move) {
        if (isGameover() || move.getMark() != turn.getPlayerStone()) {
            return false;
        }
        int rowIndex = move.getRowIndex();
        int columnIndex = move.getColumnIndex();

        return board.isEmptyField(rowIndex, columnIndex);
    }

    /**
     * Makes the specified move and updates the game state.
     * @param move the move to be played
     */
    /*@ requires isValidMove(move);
      @ ensures board.getField(move.getRowIndex(), move.getColumnIndex()) == move.getMark();
      @ ensures turn != \old(turn);
      @*/
    @Override
    public synchronized void doMove(Move move) {
        int rowIndex = move.getRowIndex();
        int columnIndex = move.getColumnIndex();
        board.setField(rowIndex, columnIndex, turn.getPlayerStone());
        if (turn == player1) {
            turn = player2;
        } else {
            turn = player1;
        }
    }

    /**
     * Checks if the game is over.
     * @return true if the game is over, false otherwise
     */
    /*@ ensures \result == board.gameOver();
      @*/
    @Override
    public synchronized boolean isGameover() {
        return board.gameOver();
    }

    /**
     * Resets the game board and sets the turn to player1.
     */
    /*@ ensures turn == player1;
      @ ensures board.reset();
      @*/
    @Override
    public synchronized void clearGameBoard() {
        turn = player1;
        board.reset();
    }

    /**
     * Returns the player who won the match.
     * @return the winner, or null if no winner yet
     */
    /*@ ensures \result != null ==> board.isWinner(\result.getPlayerStone());
      @*/
    @Override
    public synchronized Player getWinner() {
        if (turn.equals(player2)) {
            if (board.isWinner(player1.getPlayerStone())) {
                return player1;
            }
            if (board.isWinner(player2.getPlayerStone())) {
                return player2;
            }
        } else {
            if (board.isWinner(player2.getPlayerStone())) {
                return player2;
            }
            if (board.isWinner(player1.getPlayerStone())) {
                return player1;
            }
        }
        return null;
    }

    /**
     * Returns a string representation of the current game state, including the board and whose turn it is.
     * @return a string representing the game state
     */
    /*@ ensures \result != null;
      @ ensures \result.contains(turn.getName());
      @*/
    @Override
    public synchronized String toString() {
        StringBuilder boardString = new StringBuilder();
        int boardDimension = this.boardDimension;

        // Loop through rows
        for (int i = 0; i < boardDimension * 2 - 1; i++) {
            for (int j = 0; j < boardDimension * 2 - 1; j++) {
                if (i % 2 == 0) {
                    if (j % 2 == 0) {
                        // Print index or cell content for even rows/columns
                        boardString.append(" ").append(board.getField(i / 2, j / 2).toString())
                                .append(" ");
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

    /**
     * Gets the scanner used for the game input.
     * @return the scanner for input
     */
    public Scanner getGameScanner() {
        return gameScanner;
    }

    /**
     * Sets the scanner for the game.
     * @param gameScanner the scanner to be used for input
     */
    public void setGameScanner(Scanner gameScanner) {
        this.gameScanner = gameScanner;
    }

    /**
     * Closes the game scanner.
     */
    public void closeGameScanner() {
        gameScanner.close();
    }

    /**
     * Returns the dimension of the game board.
     * @return the board dimension
     */
    public synchronized int getGameDimensions() { return this.boardDimension; }

    /**
     * Returns the current game board.
     * @return the board
     */
    public synchronized Board getBoard() { return this.board; }

    /**
     * Returns the first player.
     * @return player1
     */
    public synchronized Player getPlayer1() {
        return this.player1;
    }

    /**
     * Returns the second player.
     * @return player2
     */
    public synchronized Player getPlayer2() {
        return this.player2;
    }
}
