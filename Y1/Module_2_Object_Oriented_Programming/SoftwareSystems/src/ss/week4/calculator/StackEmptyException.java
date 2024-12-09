package ss.week4.calculator;

/**
 * Exception thrown by the {@link Calculator} when there are not enough values on the stack.
 * For example calling pop() when the stack is empty, or add(), sub(), mult(), div() when fewer than two
 * values are on the stack.
 */
public class StackEmptyException extends Exception {
    public StackEmptyException(String message) {
        super(message);
    }
}
