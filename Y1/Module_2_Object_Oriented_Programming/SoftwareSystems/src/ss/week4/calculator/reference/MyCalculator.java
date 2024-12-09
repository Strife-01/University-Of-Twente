package ss.week4.calculator.reference;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import ss.week4.DoublyLinkedList;
import ss.week4.calculator.DivideByZeroException;
import ss.week4.calculator.StackEmptyException;

public class MyCalculator implements ss.calculator.Calculator {
    List<Double> list = new LinkedList<>();

    /**
     * Push the given value on the stack.
     *
     * @param value the value to push on the stack
     */
    @Override
    public void push(double value) {
        list.add(value);
    }

    /**
     * Pop a value from the stack.
     *
     * @return the value that was on the top of the stack
     * @throws StackEmptyException if the stack is empty
     */
    @Override
    public double pop() throws StackEmptyException {
        if (list.isEmpty()) {
            throw new StackEmptyException("The stack is empty");
        }
        return list.removeLast();
    }

    /**
     * Checks first value from the stack, but it doesn't mutate the stack.
     *
     * @return the value that is on the top of the stack
     * @throws StackEmptyException if the stack is empty
     */
    @Override
    public double peek() throws StackEmptyException {
        if (list.isEmpty()) {
            throw new StackEmptyException("The stack is empty...");
        }
        return list.getLast();
    }

    /**
     * Remove two values from the top of the stack, add them, then push the result on top of the stack.
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    @Override
    public void add() throws StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to add");
        }
        push(pop() + pop());
    }

    /**
     * Remove value a from top of the stack, then value b from top of the stack,
     * then compute b-a and push the result on top of the stack
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    @Override
    public void sub() throws StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to add");
        }
        double x = pop();
        double y = pop();
        push(y - x);
    }

    /**
     * Remove two values from the top of the stack, multiply them, then push the result on top of the stack
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    @Override
    public void mult() throws StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to add");
        }
        push(pop() * pop());
    }

    /**
     * Remove value a from top of the stack, then value b from top of the stack,
     * then compute b/a  and push the result on top of the stack
     * If a was zero, then push the value "Double.NaN" on top of the stack and throw the exception.
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException   if the stack does not have at least two values
     * @throws DivideByZeroException if value a had value 0
     */
    @Override
    public void div() throws DivideByZeroException, StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to add");
        }
        double x = pop();
        double y = pop();
        if (x == 0) {
            push(Double.NaN);
            throw new DivideByZeroException("/0 :(((");
        }
        push(y / x);
    }

    /**
     * Remove value a from top of the stack, then value b from top of the stack,
     * then compute b%a  and push the result on top of the stack
     * If a was zero, then push the value "Double.NaN" on top of the stack and throw the exception.
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException   if the stack does not have at least two values
     * @throws DivideByZeroException if value a had value 0
     */
    @Override
    public void mod() throws DivideByZeroException, StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to perform modulo");
        }
        double x = pop();
        double y = pop();
        if (x == 0) {
            push(Double.NaN);
            throw new DivideByZeroException("Modulo by zero is undefined");
        }
        push(y % x);
    }

    /**
     * Checks value a from top of the stack,
     * then pushes a duplicate on top of the stack
     * If less than 1 value then a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least one value
     */
    @Override
    public void dup() throws StackEmptyException {
        if (list.isEmpty()) {
            throw new StackEmptyException("The list is empty..");
        }
        push(peek());
    }
}
