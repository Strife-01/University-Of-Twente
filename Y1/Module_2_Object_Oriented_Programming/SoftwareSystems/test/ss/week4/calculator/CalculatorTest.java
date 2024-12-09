package ss.week4.calculator;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.week4.calculator.DivideByZeroException;
import ss.week4.calculator.StackEmptyException;
import ss.week4.calculator.reference.MyCalculator;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;


@Disabled
class CalculatorTest {
    private ss.calculator.Calculator calculator;

    @BeforeEach
    void setup() {
        // Create a new calculator before each test
        calculator = new MyCalculator(); // FIXME replace with the actual calculator
    }

    @Test
    void testPushPop() throws StackEmptyException {
        // Simple test: if we push the value 0.5, do we also get it back?
        calculator.push(0.5);
        assertEquals(0.5, calculator.pop());

        // Test a bunch of random numbers in a random order...
        List<Double> exampleNumbers = new ArrayList<>();
        var rand = new Random();
        for (int i=0; i<10; i++) {
            exampleNumbers.add(rand.nextDouble());
        }

        for (int i=0; i<10; i++) {
            calculator.push(exampleNumbers.get(i));
        }

        for (int i=9; i>=0; i--) {
            assertEquals(exampleNumbers.get(i), calculator.pop(), 0.01);
        }

        // Test exceptions
        assertThrows(StackEmptyException.class, () -> calculator.pop());
    }

    @Test
    void testAdd() throws StackEmptyException {
        // Also test proper handling of the stack
        // after these, stack will be: { 100, 200, -100, -300 }
        // so the first add adds -100 and -300 (= -400)
        // and the second add adds 100 and 200 (= 300)
        calculator.push(100);
        calculator.push(200);
        calculator.push(-100);
        calculator.push(-300);
        calculator.add();
        assertEquals(-400, calculator.pop());
        calculator.add();
        assertEquals(300, calculator.pop());

        // Now add some numbers
        calculator.push(4);
        calculator.push(7);
        calculator.push(1);
        calculator.push(8);
        calculator.push(3);
        calculator.push(5);
        calculator.push(2);
        calculator.push(9);
        calculator.push(6);
        calculator.add();
        calculator.add();
        calculator.add();
        calculator.add();
        calculator.add();
        calculator.add();
        calculator.add();
        calculator.add();
        // adding 1+2+3+4+5+6+7+8+9 (in any order) = 45
        assertEquals(45, calculator.pop());
        assertThrows(StackEmptyException.class, () -> calculator.pop());
    }

    @Test
    void testSub() throws StackEmptyException {
        // test if 100-0=100
        calculator.push(100);
        calculator.push(0);
        calculator.sub();
        assertEquals(100, calculator.pop());

        // test if 0-100=-100
        calculator.push(0);
        calculator.push(100);
        calculator.sub();
        assertEquals(-100, calculator.pop());
    }

    @Test
    void testMult() throws StackEmptyException {
        calculator.push(5);
        calculator.push(9);
        calculator.mult();
        assertEquals(45, calculator.pop());
        assertThrows(StackEmptyException.class, () -> calculator.pop());
    }

    @Test
    void testDiv() throws StackEmptyException, DivideByZeroException {
        // test if we get a divide by zero exception
        calculator.push(100);
        calculator.push(0);
        assertThrows(DivideByZeroException.class, () -> calculator.div());
        // after a divide by zero exception, the stack should be size 1 with only Double.NaN on top
        assertEquals(Double.NaN, calculator.pop());
        assertThrows(StackEmptyException.class, () -> calculator.pop());

        // now test a proper division 100/6
        calculator.push(100);
        calculator.push(6);
        calculator.div();
        assertEquals(100.0/6, calculator.pop());
        assertThrows(StackEmptyException.class, () -> calculator.pop()); // and test if stack now empty
    }

    @Test
    void testPeek() throws StackEmptyException {
        // Test if peek correctly returns the top of the stack without removing it
        calculator.push(42.0);
        assertEquals(42.0, calculator.peek());
        assertEquals(42.0, calculator.peek()); // Ensures peek does not remove the value
        assertEquals(42.0, calculator.pop()); // Stack still contains the value

        // Test multiple pushes and peeks
        calculator.push(1.0);
        calculator.push(2.0);
        assertEquals(2.0, calculator.peek());
        assertEquals(2.0, calculator.pop());
        assertEquals(1.0, calculator.peek());
        assertEquals(1.0, calculator.pop());

        // Test exception when peeking from an empty stack
        assertThrows(StackEmptyException.class, () -> calculator.peek());
    }

    @Test
    void testMod() throws StackEmptyException, DivideByZeroException {
        // Test normal modulo operation
        calculator.push(10);
        calculator.push(3);
        calculator.mod();
        assertEquals(10 % 3, calculator.pop());

        // Test modulo by zero
        calculator.push(10);
        calculator.push(0);
        assertThrows(DivideByZeroException.class, () -> calculator.mod());
        assertEquals(Double.NaN, calculator.pop()); // Stack contains NaN after divide-by-zero

        // Test exception for insufficient stack size
        calculator.push(10);
        assertThrows(StackEmptyException.class, () -> calculator.mod());

        // Test sequential modulo operations
        calculator.push(100);
        calculator.push(7);
        calculator.push(5);
        calculator.mod(); // 7 % 5 = 2
        calculator.mod(); // 100 % 2 = 0
        assertEquals(0, calculator.pop());
    }

    @Test
    void testDup() throws StackEmptyException {
        // Test duplicating a single value
        calculator.push(42.0);
        calculator.dup();
        assertEquals(42.0, calculator.pop());
        assertEquals(42.0, calculator.pop());

        // Test duplicating multiple values
        calculator.push(10.0);
        calculator.push(20.0);
        calculator.dup();
        assertEquals(20.0, calculator.pop()); // Duplicate
        assertEquals(20.0, calculator.pop()); // Original
        assertEquals(10.0, calculator.pop()); // Bottom of stack

        // Test exception for an empty stack
        assertThrows(StackEmptyException.class, () -> calculator.dup());
    }
}
