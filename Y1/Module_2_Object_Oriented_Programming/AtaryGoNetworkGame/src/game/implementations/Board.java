package game.implementations;

import game.utils.Stone;
import java.util.*;

/**
 * Represents the board where we place the Stones.
 */
public class Board {
    public static int DIM = 7;
    private final List<Stone> board;
    private final int boardLength;

    /**
     * Sets up the board with a given dimension.
     * Board length = dim * dim
     * @param dim dimension of the board.
     */
    /*@
        requires dim > 0;
        ensures dim > 0 ==> (\forall int i; 0 <= i && i < dim * dim; board.get(i) == Stone.EMPTY);
    */
    public Board(int dim) {
        DIM = dim;
        boardLength = DIM * DIM;
        board = new ArrayList<Stone>(boardLength);
        for (int i = 0; i < boardLength; i++) {
            board.add(Stone.EMPTY);
        }
    }

    /**
     * Empty constructor.
     * Calls the normal constructor with a default dimension 3.
     */
    public Board() {
        this(7);
    }

    /**
     * Returns the index in the board where the imagined 2 dimensional array element is placed.
     * @param i line index
     * @param j column index
     * @return array index or -1 if not correct indexes
     */
    /*@
        requires i >= 0 && j >= 0;
        requires i < DIM && j < DIM;
        ensures i < DIM && j < DIM && i >= 0 && j >= 0 ==> \result == i * DIM + j;
        ensures i < DIM || j < DIM || i < 0 || j < 0 ==> \result == -1;
        pure
    */
    public int index(int i, int j) {
        return 0 <= i && i < DIM && 0 <= j && j < DIM ? i * DIM + j : -1;
    }

    /**
     * Checks if the given coordinates for the board are valid.
     * @param i row index
     * @param j column index
     * @return true if the indexes are valid false otherwise
     */
    /*@
        requires i >= 0 && j >= 0;
        requires i < DIM && j < DIM;
        ensures i < DIM && j < DIM && i >= 0 && j >= 0 ==> \result == true;
        ensures i < DIM || j < DIM || i < 0 || j < 0 ==> \result == false;
        pure
    */
    public boolean isField(int i, int j) {
        return 0 <= i && i < DIM && 0 <= j && j < DIM;
    }

    /**
     * Checks if the given index is a valid index for the board array.
     * @param i index
     * @return true if i valid index for board
     */
    /*@
        requires i >= 0 && i < board.size();
        ensures i >= 0 && i < board.size() ==> \result == true;
        pure
    */
    public boolean isField(int i) {
        return 0 <= i && i < board.size();
    }

    /**
     * Checks if a given index represents an empty space in the board array.
     * @param index index
     * @return true if board[index] is empty.
     */
    /*@
        requires isField(index) == true;
        ensures isField(index) == true && board.get(index) == Stone.EMPTY
        ==> \result == true;
        pure
    */
    public boolean isEmptyField(int index) {
        return isField(index) && getField(index) == Stone.EMPTY;
    }

    /**
     * Checks if the imagined 2-dimensional array from board is empty on row i column j.
     * @param i row index
     * @param j column index
     * @return true if the board is empty at provided indexes
     */
    /*@
        requires isField(i, j) == true;
        ensures isField(i, j) == true && getField(i, j) == Stone.EMPTY ==> \result == true;
        pure
    */
    public boolean isEmptyField(int i, int j) {
        return isField(i, j) && getField(i, j) == Stone.EMPTY;
    }

    /**
     * Checks if the board is full.
     * @return true if the board is full.
     */
    /*@
        ensures (\forall int i; 0 <= i && i < board.size();
        getField(i) != Stone.EMPTY) ==> \result == true;
        pure
    */
    public boolean isFull() {
        for (Stone s : board) {
            if (s == Stone.EMPTY) {
                return false;
            }
        }
        return true;
    }

    public boolean gameOver() {
        return hasWinner() || isFull();
    }

    /**
     * Checks if the game has a winner.
     * @return true if winner exist
     */
    /*@
        ensures isWinner(Stone.BLACK) || isWinner(Stone.WHITE) ==> \result == true;
        pure
    */
    public boolean hasWinner() {
        return isWinner(Stone.BLACK) || isWinner(Stone.WHITE);
    }

    /**
     * Verifies if a certain Stone wins.
     * @param stone stone to check
     * @return true if the Stone is a winner
     */
    /*@
        requires stone instanceof Stone;
        ensures stone instanceof Stone
        ==> \result == true;
    */
    public boolean isWinner(Stone stone) {
        Stone s = stone.equals(Stone.BLACK) ? Stone.WHITE : Stone.BLACK;
        Map<Integer, Boolean> visited = new HashMap<>();

        for (int i = 0; i < board.size(); i++) {
            visited.put(i, false);
        }

        List<Integer> chain;

        for (int i = 0; i < board.size(); i++) {
            if (board.get(i).equals(s) && !visited.get(i)) {
                chain = getChain(board, visited, s, getRow(i), getCol(i));
                if (isChainCaptured(chain)) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * Returns the chain of stones connected to the starting stone.
     * @param board the current board configuration
     * @param visited map of visited stones, used to avoid reprocessing
     * @param startingStone the stone type (black/white) to start the chain
     * @param row the starting row position
     * @param col the starting column position
     * @return the list of indices representing the chain of connected stones
     */
    /*@ requires board != null;
      @ requires visited != null;
      @ requires startingStone != null;
      @ requires row >= 0 && row < DIM;
      @ requires col >= 0 && col < DIM;
      @ ensures \result != null;
      @ ensures \result.size() > 0;
    */
    public List<Integer> getChain(List<Stone> board, Map<Integer, Boolean> visited,
                                  Stone startingStone, int row, int col) {
        List<Integer> chain = new ArrayList<>();
        Queue<Integer> queue = new LinkedList<>();

        int startIndex = index(row, col); // Initial stone index
        queue.add(startIndex);
        visited.put(startIndex, true);  // Mark the starting stone as visited
        chain.add(startIndex);

        // Directions: up, down, left, right (4 possible directions in Go)
        int[] directions = {-1, 1, 0, 0}; // Row offset (up, down)
        int[] colOffsets = {0, 0, -1, 1};  // Column offset (left, right)

        while (!queue.isEmpty()) {
            int currentIndex = queue.remove();
            int tempRow = currentIndex / DIM;
            int tempCol = currentIndex % DIM;

            // Explore all 4 directions
            for (int i = 0; i < 4; i++) {
                int newRow = tempRow + directions[i];
                int newCol = tempCol + colOffsets[i];

                // Check if the new position is within bounds
                if (newRow >= 0 && newRow < DIM && newCol >= 0 && newCol < DIM) {
                    int neighborIndex = index(newRow, newCol);

                    // Check if the stone matches the starting stone and is not visited
                    if (board.get(neighborIndex).equals(startingStone) && !visited.getOrDefault(neighborIndex, false)) {
                        queue.add(neighborIndex);  // Add to queue
                        visited.put(neighborIndex, true);  // Mark as visited
                        chain.add(neighborIndex);  // Add to chain
                    }
                }
            }
        }

        return chain;
    }

    /**
     * Checks if a given chain of stones is captured.
     * A chain is captured if all of its liberties are blocked (i.e., no empty spaces around it).
     * @param chain the chain of stone indices to check
     * @return true if the chain is captured, false otherwise
     */
    /*@ requires chain != null;
      @ ensures \result == (\exists int i; 0 <= i < chain.size() && !anyLibertiesFree(chain.get(i)));
    */
    public boolean isChainCaptured(List<Integer> chain) {
        if (chain.isEmpty())  { return false; }

        for (int i = 0; i < chain.size(); i++) {
            if (anyLibertiesFree(chain.get(i))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Checks if there are any liberties (empty spaces) around a stone at the given index.
     * A liberty is defined as an empty adjacent spot to the stone.
     * @param index the index of the stone to check
     * @return true if there are liberties, false otherwise
     */
    /*@ requires index >= 0 && index < DIM * DIM;
      @ ensures \result == (board.get(index(row, col)) == Stone.EMPTY);
    */
    public boolean anyLibertiesFree(int index){
        int row = getRow(index);
        int col = getCol(index);

        // Check all four possible neighbors: up, down, left, right
        if (row > 0 && board.get(index(row - 1, col)).equals(Stone.EMPTY)) {
            return true; // Check above
        }
        if (row < DIM - 1 && board.get(index(row + 1, col)).equals(Stone.EMPTY)) {
            return true; // Check below
        }
        if (col > 0 && board.get(index(row, col - 1)).equals(Stone.EMPTY)) {
            return true; // Check left
        }
        if (col < DIM - 1 && board.get(index(row, col + 1)).equals(Stone.EMPTY)) {
            return true; // Check right
        }

        return false; // No liberties found
    }

    /**
     * Returns the row index from the given stone index.
     * @param index the index of the stone
     * @return the row of the stone
     */
    /*@ ensures \result == index / DIM;
    */
    public int getRow(int index) {
        return index / DIM;
    }

    /**
     * Returns the column index from the given stone index.
     * @param index the index of the stone
     * @return the column of the stone
     */
    /*@ ensures \result == index % DIM;
    */
    public int getCol(int index) {
        return index % DIM;
    }

    /**
     * Sets a Stone at a given index in the board array.
     * @param index board
     * @param s stone
     */
    /*@
        requires isField(index);
        requires s instanceof Stone;
        ensures isField(index) && s instanceof Stone ==> getField(index) == s;
    */
    public void setField(int index, Stone s) {
        if (isField(index)) {
            board.set(index, s);
        }
    }

    /**
     * Sets a Stone at the row i and column j for the imagined 2-dimensional board array.
     * @param i row index
     * @param j column index
     * @param s Stone to be set
     */
    /*@
        requires isField(i, j);
        requires s instanceof Stone;
        ensures isField(i, j) && s instanceof Stone ==> getField(i, j) == s;
    */
    public void setField(int i, int j, Stone s) {
        if (isField(i, j)) {
            setField(i * DIM + j, s);
        }
    }

    /**
     * Retrieves the Stone at a given index in the board array.
     * @param index for retrieval
     * @return Stone at index
     */
    /*@
        requires isField(index);
        ensures isField(index) ==> \result == board.get(index);
        pure
    */
    public Stone getField(int index) {
        return isField(index) ? board.get(index) : Stone.EMPTY;
    }

    /**
     * Returieves the Stone at the row i and column j of an imagined 2-dimensional array.
     * @param i row index
     * @param j column index
     * @return returned Stone
     */
    /*@
        requires isField(i, j) == true;
        ensures isField(i, j) == true ==> \result == board.get(i * DIM + j);
        pure
    */
    public Stone getField(int i, int j) {
        return isField(i, j) ? getField(i * DIM + j) : Stone.EMPTY;
    }

    /**
     * Creates a deep copy of the board.
     * @return the copy
     */
    /*@
        ensures (\forall int i; 0 <= i && i < board.size(); \result.board.get(i) == getField(i));
        ensures \result.DIM == DIM;
    */
    public Board deepCopy() {
        Board copy = new Board(DIM);
        for (int i = 0; i < board.size(); i++) {
            copy.board.set(i, this.board.get(i));
        }
        return copy;
    }

    /**
     * Resets the board.
     */
    /*@
        ensures (\forall int i; 0 <= i && i < board.size(); getField(i) == Stone.EMPTY);
    */
    public void reset() {
        board.replaceAll(ignored -> Stone.EMPTY);
    }

    /**
     * Returns a copy of the board.
     * @return a list of stones representing the current board configuration
     */
    /*@ ensures \result != null;
      @ ensures \result.size() == boardLength;
      @*/
    public List<Stone> getBoard() {
        return new ArrayList<>(this.board);
    }

    /**
     * Returns a list of indices representing empty spots on the board.
     * @return a list of empty spot indices
     */
    /*@ ensures \result != null;
      @ ensures (\forall int i; 0 <= i < \result.size(); isEmptyField(\result.get(i)));
      @*/
    public List<Integer> getEmptySpots() {
        ArrayList<Integer> emptySpots = new ArrayList<>();
        for (int i = 0; i < boardLength; i++) {
            if (this.isEmptyField(i)) {
                emptySpots.add(i);
            }
        }
        return emptySpots;
    }

    /**
     * Converts the board into a string representation.
     * This method generates a textual representation of the Go board with rows and columns.
     * @return a string representation of the current board
     */
    /*@ ensures \result != null;
      @ ensures \result.length() > 0;
      @*/
    @Override
    public String toString() {
        StringBuilder boardString = new StringBuilder();
        int boardDimension = DIM;

        // Loop through rows
        for (int i = 0; i < boardDimension * 2 - 1; i++) {
            for (int j = 0; j < boardDimension * 2 - 1; j++) {
                if (i % 2 == 0) {
                    if (j % 2 == 0) {
                        // Print index or cell content for even rows/columns
                        boardString.append(" ").append(getField(i / 2, j / 2).toString())
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
        return boardString.toString();
    }
}

