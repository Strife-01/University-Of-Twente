package ss;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import ss.week1.BrokenFibonacci;

public class BrokenFibonacciTest {
    @Test
    void fibonacciTestBase() {
        Assertions.assertEquals(0, BrokenFibonacci.fibonacci(0));
        Assertions.assertEquals(1, BrokenFibonacci.fibonacci(1));
        Assertions.assertEquals(1, BrokenFibonacci.fibonacci(2));
    }

    @Test
    void fibonacciTestHigher() {
        Assertions.assertEquals(2, BrokenFibonacci.fibonacci(3));
        Assertions.assertEquals(3, BrokenFibonacci.fibonacci(4));
        Assertions.assertEquals(5, BrokenFibonacci.fibonacci(5));
        Assertions.assertEquals(8, BrokenFibonacci.fibonacci(6));
        Assertions.assertEquals(13, BrokenFibonacci.fibonacci(7));
        Assertions.assertEquals(21, BrokenFibonacci.fibonacci(8));
        Assertions.assertEquals(4181, BrokenFibonacci.fibonacci(19));
        Assertions.assertEquals(701408733, BrokenFibonacci.fibonacci(44));
    }
}
