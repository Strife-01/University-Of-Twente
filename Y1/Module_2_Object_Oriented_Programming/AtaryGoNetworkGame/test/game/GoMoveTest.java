package game;

import game.implementations.GoMove;
import game.utils.Stone;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test suite for the {@link GoMove} class.
 * This class tests the initialization of the GoMove object and verifies that its properties are correctly set.
 */
public class GoMoveTest {

    /**
     * Test case for verifying the correct initialization of a {@link GoMove}.
     * Ensures that the row index, column index, and stone mark are correctly set.
     */
    @Test
    public void testGoMoveInitialization() {
        int rowIndex = 3;
        int columnIndex = 4;
        Stone stone = Stone.BLACK;  // assuming Stone is an enum with BLACK and WHITE

        GoMove move = new GoMove(rowIndex, columnIndex, stone);

        assertEquals(rowIndex, move.getRowIndex(), "Row index should be correctly initialized.");
        assertEquals(columnIndex, move.getColumnIndex(), "Column index should be correctly initialized.");
        assertEquals(stone, move.getMark(), "Stone should be correctly initialized.");
    }

    /**
     * Test case for verifying that different {@link GoMove} objects have distinct values.
     * Ensures that each move has unique row index, column index, and stone mark.
     */
    @Test
    public void testGoMoveValues() {
        GoMove move1 = new GoMove(1, 1, Stone.BLACK);
        GoMove move2 = new GoMove(2, 2, Stone.WHITE);

        assertNotEquals(move1.getRowIndex(), move2.getRowIndex(), "Row indices should not be equal for different moves.");
        assertNotEquals(move1.getColumnIndex(), move2.getColumnIndex(), "Column indices should not be equal for different moves.");
        assertNotEquals(move1.getMark(), move2.getMark(), "Stones should be different for different moves.");
    }
}
