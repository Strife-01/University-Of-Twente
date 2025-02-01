package game.implementations;

import game.interfaces.Game;
import game.interfaces.Move;
import game.interfaces.Player;
import game.utils.Stone;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

import java.util.List;

/**
 * Test suite for the {@link GoGame} class.
 * This class tests the core gameplay mechanics, turn management, move validation, and game board clearing.
 */
public class GoGameTest {

    private GoGame game;
    private Player player1;
    private Player player2;
    private Move mockMove;

    /**
     * Sets up the test environment by creating mock players and a mock move,
     * and initializing the game instance before each test.
     */
    @BeforeEach
    public void setUp() {
        player1 = mock(Player.class);
        player2 = mock(Player.class);
        mockMove = mock(Move.class);

        when(player1.getPlayerStone()).thenReturn(Stone.BLACK);
        when(player2.getPlayerStone()).thenReturn(Stone.WHITE);
        when(player1.getName()).thenReturn("Player 1");
        when(player2.getName()).thenReturn("Player 2");

        game = new GoGame(7, player1, player2);
    }

    /**
     * Test case for verifying the correct turn order.
     * Ensures that Player 1 starts and the turn alternates after each move.
     */
    @Test
    public void testGetTurn() {
        assertEquals(player1, game.getTurn(), "It should be Player 1's turn initially.");
        game.doMove(mockMove);  // Player 1 plays
        assertEquals(player2, game.getTurn(), "After Player 1's move, it should be Player 2's turn.");
    }

    /**
     * Test case for retrieving valid moves for the current turn.
     * Ensures that there is at least one valid move initially.
     */
    @Test
    public void testGetValidMoves() {
        List<Move> validMoves = game.getValidMoves();
        assertNotNull(validMoves, "Valid moves list should not be null.");
        assertTrue(validMoves.size() > 0, "There should be at least one valid move initially.");
    }

    /**
     * Test case for validating a valid move by Player 1.
     * Ensures that Player 1 can place a stone on an empty spot.
     */
    @Test
    public void testIsValidMove_validMove() {
        when(mockMove.getRowIndex()).thenReturn(0);
        when(mockMove.getColumnIndex()).thenReturn(0);
        when(mockMove.getMark()).thenReturn(Stone.BLACK);

        assertTrue(game.isValidMove(mockMove), "Move should be valid if the spot is empty and it's Player 1's turn.");
    }

    /**
     * Test case for validating an invalid move when Player 2 tries to play.
     * Ensures that Player 2 cannot place a stone when it's Player 1's turn.
     */
    @Test
    public void testIsValidMove_invalidMove() {
        when(mockMove.getRowIndex()).thenReturn(0);
        when(mockMove.getColumnIndex()).thenReturn(0);
        when(mockMove.getMark()).thenReturn(Stone.WHITE);

        assertFalse(game.isValidMove(mockMove), "Move should be invalid if it's not Player 1's turn.");
    }

    /**
     * Test case for performing a valid move.
     * Ensures that the stone is placed correctly on the board after the move.
     */
    @Test
    public void testDoMove() {
        when(mockMove.getRowIndex()).thenReturn(0);
        when(mockMove.getColumnIndex()).thenReturn(0);
        when(mockMove.getMark()).thenReturn(Stone.BLACK);

        game.doMove(mockMove);
        assertEquals(Stone.BLACK, game.getBoard().getField(0, 0), "After the move, the stone at position (0, 0) should be BLACK.");
    }

    /**
     * Test case to check the game-over condition when the game is not over.
     * Ensures that the game is not over at the start.
     */
    @Test
    public void testIsGameover_whenGameNotOver() {
        assertFalse(game.isGameover(), "The game should not be over at the start.");
    }

    /**
     * Test case for clearing the game board.
     * Ensures that after clearing the board, all fields are empty and the turn returns to Player 1.
     */
    @Test
    public void testClearGameBoard() {
        // Perform a move
        when(mockMove.getRowIndex()).thenReturn(0);
        when(mockMove.getColumnIndex()).thenReturn(0);
        when(mockMove.getMark()).thenReturn(Stone.BLACK);
        game.doMove(mockMove);

        // Reset the board
        game.clearGameBoard();
        assertEquals(Stone.EMPTY, game.getBoard().getField(0, 0), "After clearing the game board, all fields should be empty.");
        assertEquals(player1, game.getTurn(), "After clearing the board, it should be Player 1's turn.");
    }
}
