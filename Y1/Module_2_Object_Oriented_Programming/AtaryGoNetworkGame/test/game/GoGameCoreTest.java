package game;

import java.util.HashMap;
import org.junit.jupiter.api.*;
import static org.junit.jupiter.api.Assertions.*;
import game.implementations.*;
import game.utils.Stone;
import game.interfaces.Move;
import java.util.List;

/**
 * Test suite for the Go game implementation focusing on core game mechanics,
 * board state management, and game rules.
 */
public class GoGameCoreTest {
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
     * Tests basic board initialization and state
     */
    @Test
    void testBoardInitialization() {
        assertEquals(7, Board.DIM);
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                assertEquals(Stone.EMPTY, board.getField(i, j));
            }
        }
    }

    /**
     * Tests move validation logic
     */
    @Test
    void testMoveValidation() {
        // Test valid move
        Move validMove = new GoMove(0, 0, Stone.BLACK);
        assertTrue(game.isValidMove(validMove));

        // Test move on occupied space
        game.doMove(validMove);
        assertFalse(game.isValidMove(validMove));

        // Test move out of bounds
        Move invalidMove = new GoMove(7, 7, Stone.BLACK);
        assertFalse(game.isValidMove(invalidMove));

        // Test move with wrong stone color
        Move wrongColorMove = new GoMove(1, 1, Stone.BLACK);
        assertFalse(game.isValidMove(wrongColorMove));
    }

    /**
     * Tests stone capturing mechanics
     */
    @Test
    void testStoneCapturing() {
        // Set up a capture scenario
        // Place white stone at center
        board.setField(3, 3, Stone.WHITE);

        // Surround with black stones
        board.setField(2, 3, Stone.BLACK);
        board.setField(4, 3, Stone.BLACK);
        board.setField(3, 2, Stone.BLACK);

        // Complete the capture with final black stone
        Move captureMove = new GoMove(3, 4, Stone.BLACK);
        assertTrue(game.isValidMove(captureMove));
        game.doMove(captureMove);

        // Verify white stone is captured (chain check)
        assertTrue(board.isWinner(Stone.BLACK));
    }

    /**
     * Tests the chain detection logic
     */
    @Test
    void testChainDetection() {
        // Create a chain of stones
        board.setField(1, 1, Stone.BLACK);
        board.setField(1, 2, Stone.BLACK);
        board.setField(1, 3, Stone.BLACK);

        // Create visited map and test chain detection
        List<Integer> chain = board.getChain(board.getBoard(), new HashMap<>(), Stone.BLACK, 1, 1);
        assertEquals(3, chain.size());
        assertTrue(chain.contains(board.index(1, 1)));
        assertTrue(chain.contains(board.index(1, 2)));
        assertTrue(chain.contains(board.index(1, 3)));
    }

    /**
     * Tests game end conditions
     */
    @Test
    void testGameEndConditions() {
        // Test game not over at start
        assertFalse(game.isGameover());
        assertNull(game.getWinner());

        // Create a winning condition by capturing stones
        board.setField(0, 0, Stone.WHITE);
        board.setField(0, 1, Stone.BLACK);
        board.setField(1, 0, Stone.BLACK);
        board.setField(1, 1, Stone.BLACK);

        // The game should detect a winner
        assertTrue(board.hasWinner());
        assertNotNull(game.getWinner());
    }

    /**
     * Tests liberty checking
     */
    @Test
    void testLibertyChecking() {
        // Place a stone with all liberties free
        board.setField(3, 3, Stone.BLACK);
        assertTrue(board.anyLibertiesFree(board.index(3, 3)));

        // Surround the stone partially
        board.setField(2, 3, Stone.WHITE);
        board.setField(4, 3, Stone.WHITE);
        board.setField(3, 2, Stone.WHITE);

        // Stone should still have one liberty
        assertTrue(board.anyLibertiesFree(board.index(3, 3)));

        // Complete the surrounding
        board.setField(3, 4, Stone.WHITE);

        // Stone should now have no liberties
        assertFalse(board.anyLibertiesFree(board.index(3, 3)));
    }

    /**
     * Tests turn management
     */
    @Test
    void testTurnManagement() {
        assertEquals(player1, game.getTurn());

        Move move = new GoMove(0, 0, Stone.BLACK);
        game.doMove(move);

        assertEquals(player2, game.getTurn());

        move = new GoMove(0, 1, Stone.WHITE);
        game.doMove(move);

        assertEquals(player1, game.getTurn());
    }

    /**
     * Tests board reset functionality
     */
    @Test
    void testBoardReset() {
        // Make some moves
        game.doMove(new GoMove(0, 0, Stone.BLACK));
        game.doMove(new GoMove(0, 1, Stone.WHITE));

        // Reset the board
        game.clearGameBoard();

        // Verify board is empty
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                assertEquals(Stone.EMPTY, board.getField(i, j));
            }
        }

        // Verify it's player1's turn
        assertEquals(player1, game.getTurn());
    }

    /**
     * Tests board deep copy functionality
     */
    @Test
    void testBoardDeepCopy() {
        // Make some moves on original board
        board.setField(0, 0, Stone.BLACK);
        board.setField(0, 1, Stone.WHITE);

        // Create deep copy
        Board copy = board.deepCopy();

        // Verify copy has same state
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                assertEquals(board.getField(i, j), copy.getField(i, j));
            }
        }

        // Modify original board
        board.setField(1, 1, Stone.BLACK);

        // Verify copy remains unchanged
        assertEquals(Stone.EMPTY, copy.getField(1, 1));
    }
}