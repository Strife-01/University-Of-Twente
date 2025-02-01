package game;

import org.junit.jupiter.api.*;
import static org.junit.jupiter.api.Assertions.*;
import game.implementations.*;
import game.utils.Stone;
import game.interfaces.Move;
import java.util.*;

/**
 * Extended test suite for the Go game implementation covering advanced scenarios
 * and edge cases.
 */
public class GoGameAdvancedTest {
    private GoGame game;
    private HumanPlayer player1;
    private HumanPlayer player2;
    private Board board;

    @BeforeEach
    void setUp() {
        player1 = new HumanPlayer("Black", Stone.BLACK);
        player2 = new HumanPlayer("White", Stone.WHITE);
        game = new GoGame(7, player1, player2);
        board = game.getBoard();
    }

    /**
     * Tests complex chain capturing scenarios.
     */
    @Test
    void testComplexChainCapture() {
        // Create a complex chain of white stones
        board.setField(2, 2, Stone.WHITE);
        board.setField(2, 3, Stone.WHITE);
        board.setField(2, 4, Stone.WHITE);
        board.setField(3, 3, Stone.WHITE);

        // Surround with black stones
        board.setField(1, 2, Stone.BLACK);
        board.setField(1, 3, Stone.BLACK);
        board.setField(1, 4, Stone.BLACK);
        board.setField(2, 1, Stone.BLACK);
        board.setField(2, 5, Stone.BLACK);
        board.setField(3, 2, Stone.BLACK);
        board.setField(3, 4, Stone.BLACK);
        board.setField(4, 3, Stone.BLACK);

        // Verify chain is captured
        assertTrue(board.isChainCaptured(Arrays.asList(
                board.index(2, 2),
                board.index(2, 3),
                board.index(2, 4),
                board.index(3, 3)
        )));
    }

    /**
     * Tests edge and corner capture scenarios.
     */
    @Test
    void testEdgeAndCornerCaptures() {
        // Test corner capture
        board.setField(0, 0, Stone.WHITE);
        board.setField(0, 1, Stone.BLACK);
        board.setField(1, 0, Stone.BLACK);
        assertTrue(board.isChainCaptured(Collections.singletonList(board.index(0, 0))));

        // Test edge capture
        board.setField(0, 3, Stone.WHITE);
        board.setField(0, 2, Stone.BLACK);
        board.setField(0, 4, Stone.BLACK);
        board.setField(1, 3, Stone.BLACK);
        assertTrue(board.isChainCaptured(Collections.singletonList(board.index(0, 3))));
    }

    /**
     * Tests multiple chain interactions.
     */
    @Test
    void testMultipleChainInteractions() {
        // Create two separate white chains
        board.setField(1, 1, Stone.WHITE);
        board.setField(1, 2, Stone.WHITE);
        board.setField(3, 1, Stone.WHITE);
        board.setField(3, 2, Stone.WHITE);

        // Verify they're recognized as separate chains
        List<Integer> chain1 = board.getChain(board.getBoard(), new HashMap<>(), Stone.WHITE, 1, 1);
        List<Integer> chain2 = board.getChain(board.getBoard(), new HashMap<>(), Stone.WHITE, 3, 1);

        assertEquals(2, chain1.size());
        assertEquals(2, chain2.size());
        assertFalse(chain1.contains(board.index(3, 1)));
        assertFalse(chain2.contains(board.index(1, 1)));
    }

    /**
     * Tests boundary move validation.
     */
    @Test
    void testBoundaryMoveValidation() {
        // Test all board boundary positions
        for (int i = 0; i < Board.DIM; i++) {
            // Top edge
            assertTrue(game.isValidMove(new GoMove(0, i, Stone.BLACK)));
            // Bottom edge
            assertTrue(game.isValidMove(new GoMove(Board.DIM - 1, i, Stone.BLACK)));
            // Left edge
            assertTrue(game.isValidMove(new GoMove(i, 0, Stone.BLACK)));
            // Right edge
            assertTrue(game.isValidMove(new GoMove(i, Board.DIM - 1, Stone.BLACK)));
        }

        // Test invalid out-of-bounds moves
        assertFalse(game.isValidMove(new GoMove(-1, 0, Stone.BLACK)));
        assertFalse(game.isValidMove(new GoMove(0, -1, Stone.BLACK)));
        assertFalse(game.isValidMove(new GoMove(Board.DIM, 0, Stone.BLACK)));
        assertFalse(game.isValidMove(new GoMove(0, Board.DIM, Stone.BLACK)));
    }

    /**
     * Tests complex liberty scenarios.
     */
    @Test
    void testComplexLibertyScenarios() {
        // Create a "snake" of stones with multiple liberties
        board.setField(2, 2, Stone.BLACK);
        board.setField(2, 3, Stone.BLACK);
        board.setField(2, 4, Stone.BLACK);
        board.setField(3, 4, Stone.BLACK);
        board.setField(4, 4, Stone.BLACK);

        // Check liberties at different points
        assertTrue(board.anyLibertiesFree(board.index(2, 2)));
        assertTrue(board.anyLibertiesFree(board.index(2, 3)));
        assertTrue(board.anyLibertiesFree(board.index(4, 4)));

        // Add some opposing stones
        board.setField(1, 2, Stone.WHITE);
        board.setField(1, 3, Stone.WHITE);
        board.setField(1, 4, Stone.WHITE);

        // Verify liberties still exist
        assertTrue(board.anyLibertiesFree(board.index(2, 2)));
    }

    /**
     * Tests game state after multiple moves.
     */
    @Test
    void testGameStateAfterMultipleMoves() {
        List<Move> moves = Arrays.asList(
                new GoMove(0, 0, Stone.BLACK),
                new GoMove(0, 1, Stone.WHITE),
                new GoMove(1, 0, Stone.BLACK),
                new GoMove(1, 1, Stone.WHITE)
        );

        // Execute moves
        for (Move move : moves) {
            assertTrue(game.isValidMove(move));
            game.doMove(move);
        }

        // Verify board state
        assertEquals(Stone.BLACK, board.getField(0, 0));
        assertEquals(Stone.WHITE, board.getField(0, 1));
        assertEquals(Stone.BLACK, board.getField(1, 0));
        assertEquals(Stone.WHITE, board.getField(1, 1));
    }

    /**
     * Tests concurrent chain capture scenarios.
     */
    @Test
    void testConcurrentChainCapture() {
        // Set up two chains that could be captured simultaneously
        // First chain
        board.setField(1, 1, Stone.WHITE);
        board.setField(1, 2, Stone.WHITE);
        board.setField(0, 1, Stone.BLACK);
        board.setField(0, 2, Stone.BLACK);
        board.setField(2, 1, Stone.BLACK);
        board.setField(2, 2, Stone.BLACK);

        // Second chain
        board.setField(4, 4, Stone.WHITE);
        board.setField(4, 5, Stone.WHITE);
        board.setField(3, 4, Stone.BLACK);
        board.setField(3, 5, Stone.BLACK);
        board.setField(5, 4, Stone.BLACK);
        board.setField(5, 5, Stone.BLACK);

        // Complete both captures
        board.setField(1, 0, Stone.BLACK);
        board.setField(1, 3, Stone.BLACK);
        board.setField(4, 3, Stone.BLACK);
        board.setField(4, 6, Stone.BLACK);

        // Verify both chains are captured
        assertTrue(board.isWinner(Stone.BLACK));
    }

    /**
     * Tests valid moves list generation.
     */
    @Test
    void testValidMovesList() {
        // Initial board should have all positions available
        List<Move> validMoves = game.getValidMoves();
        assertEquals(Board.DIM * Board.DIM, validMoves.size());

        // Make some moves and verify list updates
        game.doMove(new GoMove(0, 0, Stone.BLACK));
        game.doMove(new GoMove(0, 1, Stone.WHITE));

        validMoves = game.getValidMoves();
        assertEquals(Board.DIM * Board.DIM - 2, validMoves.size());
    }

    /**
     * Tests the board's string representation.
     */
    @Test
    void testBoardStringRepresentation() {
        // Empty board
        String emptyBoard = board.toString();
        assertTrue(emptyBoard.contains(" "));

        // Make some moves
        board.setField(0, 0, Stone.BLACK);
        board.setField(0, 1, Stone.WHITE);

        String updatedBoard = board.toString();
        assertTrue(updatedBoard.contains("B"));
        assertTrue(updatedBoard.contains("W"));
    }
}