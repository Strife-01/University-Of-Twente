package ss.TikTakToe;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents the board where we place the marks.
 */
public class Board {
    public static int DIM = 3;
    private List<Mark> board;
    private int boardLength;

    /*@
        public invariant DIM > 0;
        private invariant board.size() == boardLength;
        private invariant (\num_of int i; 0 <= i && i < boardLength ; board.get(i) == Mark.XX) <= 5;
        private invariant (\num_of int j; 0 <= j && j < boardLength ; board.get(j) == Mark.OO) <= 5;
        private invariant (\num_of int i; 0 <= i && i < boardLength ; board.get(i) == Mark.XX) >=
        (\num_of int j; 0 <= j && j < boardLength ; board.get(j) == Mark.OO);
    */

    /**
     * Sets up the board with a given dimension.
     * Board length = dim * dim
     * @param dim dimension of the board.
     */
    /*@
        requires dim > 0;
        ensures dim > 0 ==> (\forall int i; 0 <= i && i < dim * dim; board.get(i) == Mark.EMPTY);
    */
    public Board(int dim) {
        DIM = dim;
        boardLength = DIM * DIM;
        board = new ArrayList<Mark>(boardLength);
        for (int i = 0; i < boardLength; i++) {
            board.add(Mark.EMPTY);
        }
    }

    /**
     * Empty constructor.
     * Calls the normal constructor with a default dimension 3.
     */
    /*@
        ensures this.DIM == 3;
        ensures DIM == 3 ==> (\forall int i; 0 <= i && i < DIM * DIM; board.get(i) == Mark.EMPTY);
    */
    public Board() {
        this(3);
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
        return 0 <= i && i < board.size() && 0 <= j && j < board.size() ? i * DIM + j : -1;
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
        return 0 <= i && i < board.size() && 0 <= j && j < board.size() && i * DIM + j < board.size();
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
        ensures isField(index) == true && board.get(index) == Mark.EMPTY
        ==> \result == true;
        pure
    */
    public boolean isEmptyField(int index) {
        return isField(index) && getField(index) == Mark.EMPTY;
    }

    /**
     * Checks if the imagined 2-dimensional array from board is empty on row i column j.
     * @param i row index
     * @param j column index
     * @return true if the board is empty at provided indexes
     */
    /*@
        requires isField(i, j) == true;
        ensures isField(i, j) == true && getField(i, j) == Mark.EMPTY ==> \result == true;
        pure
    */
    public boolean isEmptyField(int i, int j) {
        return isField(i, j) && getField(i, j) == Mark.EMPTY;
    }

    /**
     * Checks if the board is full.
     * @return true if the board is full.
     */
    /*@
        ensures (\forall int i; 0 <= i && i < board.size();
        getField(i) != Mark.EMPTY) ==> \result == true;
        pure
    */
    public boolean isFull() {
        for (Mark mark : board) {
            if (mark == Mark.EMPTY) {
                return false;
            }
        }
        return true;
    }

    /**
     * Checks if a given mark is present on a full row.
     * @param mark to check
     * @return true if the mark is on a full row
     */
    /*@
        requires mark instanceof Mark;
        pure
    */
    public boolean hasRow(Mark mark) {
        for (int i = 0; i < board.size(); i += DIM) {
            int counter = 0;
            for (int j = 0; j < DIM; j++) {
                if (board.get(i + j) == mark) {
                    counter++;
                }
            }
            if (counter == DIM) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks if a given mark is present on a full column.
     * @param mark to check
     * @return true if the mark is on a full column
     */
    /*@
        requires mark instanceof Mark;
        pure
    */
    public boolean hasColumn(Mark mark) {
        for (int i = 0; i < DIM; i++) {
            int counter = 0;
            for (int j = 0; j < board.size(); j += DIM) {
                if (board.get(i + j) == mark) {
                    counter++;
                }
            }
            if (counter == DIM) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks if a given mark is present on a diagonal.
     * @param mark to check
     * @return true if the mark is on a full diagonal
     */
    /*@
        requires mark instanceof Mark;
        pure
    */
    public boolean hasDiagonal(Mark mark) {
        int counter = 0;
        for (int i = 0; i < DIM; i++) {
            if (board.get(i * DIM + i) == mark) {
                counter++;
            }
        }

        if (counter == DIM) {
            return true;
        }

        counter = 0;
        for (int i = 0; i < DIM; i++) {
            for (int j = 0; j < DIM; j++) {
                if (i == DIM - j - 1 && board.get(index(i, j)) == mark) {
                    counter++;
                }
            }
        }
        return counter == DIM;
    }

    /**
     * Checks if the game is finished.
     * @return true if the game is finished
     */
    /*@
        ensures (\exists Mark m;
        m == Mark.OO || m == Mark.OO; hasRow(m) || hasColumn(m) || hasDiagonal(m)) ||
        isFull() == true ==> \result == true;
        pure
    */
    public boolean gameOver() {
        return isFull() || hasRow(Mark.OO) || hasRow(Mark.XX) || hasColumn(Mark.OO) || hasColumn(Mark.XX) ||
                hasDiagonal(Mark.OO) || hasDiagonal(Mark.XX);
    }

    /**
     * Checks if the game has a winner.
     * @return true if winner exist
     */
    /*@
        ensures isWinner(Mark.OO) || isWinner(Mark.XX) ==> \result == true;
        pure
    */
    public boolean hasWinner() {
        return isWinner(Mark.OO) || isWinner(Mark.XX);
    }

    /**
     * Verifies if a certain mark wins.
     * @param mark to check
     * @return true if the mark is a winner
     */
    /*@
        requires mark instanceof Mark;
        ensures mark instanceof Mark && (hasRow(mark) || hasColumn(mark) || hasDiagonal(mark))
        ==> \result == true;
    */
    public boolean isWinner(Mark mark) {
        return hasRow(mark) || hasColumn(mark) || hasDiagonal(mark);
    }

    /**
     * Sets a mark at a given index in the board array.
     * @param index board
     * @param mark mark
     */
    /*@
        requires isField(index);
        requires mark instanceof Mark;
        ensures isField(index) && mark instanceof Mark ==> getField(index) == mark;
    */
    public void setField(int index, Mark mark) {
        if (isField(index)) {
            board.set(index, mark);
        }
    }

    /**
     * Sets a mark at the row i and column j for the imagined 2-dimensional board array.
     * @param i row index
     * @param j column index
     * @param mark mark to be set
     */
    /*@
        requires isField(i, j);
        requires mark instanceof Mark;
        ensures isField(i, j) && mark instanceof Mark ==> getField(i, j) == mark;
    */
    public void setField(int i, int j, Mark mark) {
        if (isField(i, j)) {
            board.set(i * DIM + j, mark);
        }
    }

    /**
     * Retrieves the mark at a given index in the board array.
     * @param index for retrieval
     * @return mark at index
     */
    /*@
        requires isField(index);
        ensures isField(index) ==> \result == board.get(index);
        pure
    */
    public Mark getField(int index) {
        return isField(index) ? board.get(index) : Mark.EMPTY;
    }

    /**
     * Returieves the mark at the row i and column j of an imagined 2-dimensional array.
     * @param i row index
     * @param j column index
     * @return returned mark
     */
    /*@
        requires isField(i, j) == true;
        ensures isField(i, j) == true ==> \result == board.get(i * DIM + j);
        pure
    */
    public Mark getField(int i, int j) {
        return isField(i, j) ? board.get(i * DIM + j) : Mark.EMPTY;
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
        ensures (\forall int i; 0 <= i && i < board.size(); getField(i) == Mark.EMPTY);
    */
    public void reset() {
        board.replaceAll(ignored -> Mark.EMPTY);
    }
}
