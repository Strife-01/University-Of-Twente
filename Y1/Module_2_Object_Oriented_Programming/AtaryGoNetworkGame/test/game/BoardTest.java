package game.implementations;

import game.utils.Stone;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test suite for the {@link Board} class.
 * This class contains tests for the board's constructor, methods, and edge cases.
 */
public class BoardTest {

    private Board board;

    /**
     * Sets up the test environment by initializing a 7x7 board before each test.
     */
    @BeforeEach
    public void setUp() {
        board = new Board(7);  // Initialize a 7x7 board
    }

    /**
     * Test case for verifying the default constructor of the {@link Board} class.
     * Ensures that the default dimension is 7.
     */
    @Test
    public void testBoardConstructor_defaultSize() {
        Board defaultBoard = new Board();
        assertEquals(7, defaultBoard.DIM, "Default board should have a dimension of 7");
    }

    /**
     * Test case for verifying the custom constructor of the {@link Board} class.
     * Ensures that a custom board size is set correctly.
     */
    @Test
    public void testBoardConstructor_customSize() {
        Board customBoard = new Board(5);
        assertEquals(5, customBoard.DIM, "Custom board should have the correct dimension");
    }

    /**
     * Test case for verifying the index calculation with valid coordinates.
     * Ensures that the {@link Board#index(int, int)} method returns the correct index
     * for given coordinates (2, 3).
     */
    @Test
    public void testIndex_validCoordinates() {
        int index = board.index(2, 3);
        assertEquals(17, index, "Index for coordinates (2, 3) should be 17");  // Verify the correct index calculation
    }

    /**
     * Test case for verifying the index calculation with invalid coordinates.
     * Ensures that the {@link Board#index(int, int)} method returns -1 for out-of-bounds coordinates.
     */
    @Test
    public void testIndex_invalidCoordinates() {
        int index = board.index(7, 8);
        assertEquals(-1, index, "Invalid coordinates (7, 8) should return -1");
    }

    /**
     * Test case for checking if a field is valid on the board.
     * Ensures that the {@link Board#isField(int, int)} method correctly identifies valid fields.
     */
    @Test
    public void testIsField_validField() {
        assertTrue(board.isField(3, 4), "Coordinates (3, 4) should be valid on the board");
    }

    /**
     * Test case for checking if a field is invalid on the board.
     * Ensures that the {@link Board#isField(int, int)} method correctly identifies invalid fields.
     */
    @Test
    public void testIsField_invalidField() {
        assertFalse(board.isField(7, 8), "Coordinates (7, 8) should be invalid");
    }

    /**
     * Test case for checking if a field is empty at a given index.
     * Ensures that the {@link Board#isEmptyField(int)} method returns true for an empty field initially.
     */
    @Test
    public void testIsEmptyField() {
        assertTrue(board.isEmptyField(16), "Field at index 16 should be empty initially");
    }

    /**
     * Test case for setting a valid stone on a valid index.
     * Ensures that the {@link Board#setField(int, Stone)} method sets the correct stone on the board.
     */
    @Test
    public void testSetField_validIndex() {
        board.setField(16, Stone.BLACK);
        assertEquals(Stone.BLACK, board.getField(16), "Field at index 16 should be set to BLACK");
    }

    /**
     * Test case for attempting to set a stone at an invalid index.
     * Ensures that the {@link Board#setField(int, Stone)} method does not change the board for invalid indices.
     */
    @Test
    public void testSetField_invalidIndex() {
        board.setField(50, Stone.WHITE);
        assertEquals(Stone.EMPTY, board.getField(50), "Invalid index 50 should not set any stone");
    }

    /**
     * Test case to check if the board is not full initially.
     * Ensures that the {@link Board#isFull()} method correctly identifies if the board is not full at the start.
     */
    @Test
    public void testIsFull_whenBoardIsNotFull() {
        assertFalse(board.isFull(), "Board should not be full initially");
    }

    /**
     * Test case to check if the board is full after all spots are filled.
     * Ensures that the {@link Board#isFull()} method returns true when all spots are filled.
     */
    @Test
    public void testIsFull_whenBoardIsFull() {
        // Fill the board with stones to simulate a full board
        for (int i = 0; i < 49; i++) {
            board.setField(i, Stone.BLACK);
        }
        assertTrue(board.isFull(), "Board should be full when all spots are filled");
    }

    /**
     * Test case for resetting the board.
     * Ensures that the {@link Board#reset()} method clears all stones and returns the board to its initial state.
     */
    @Test
    public void testResetBoard() {
        board.setField(16, Stone.BLACK);
        board.reset();
        assertEquals(Stone.EMPTY, board.getField(16), "After reset, all fields should be empty");
    }

    /**
     * Test case for checking the game-over condition when the board is neither full nor has a winner.
     * Ensures that the {@link Board#gameOver()} method returns false when there is no winner and the board is not full.
     */
    @Test
    public void testGameOver_noWinnerAndNotFull() {
        assertFalse(board.gameOver(), "Game should not be over if there's no winner and board is not full");
    }

    /**
     * Test case for checking the empty spots on the board.
     * Ensures that the {@link Board#getEmptySpots()} method returns the correct list of empty spots.
     */
    @Test
    public void testGetEmptySpots() {
        board.setField(16, Stone.BLACK);
        assertFalse(board.getEmptySpots().contains(16), "Empty spots should not include the index 16 after setting a stone");
        assertTrue(board.getEmptySpots().size() == 48, "There should be 48 empty spots on a 7x7 board with one filled spot");
    }
}
