package ss.week5;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

import org.junit.jupiter.api.Test;

import ss.week5.ArgumentLengthsDifferException;
import ss.week5.TooFewArgumentsException;
import ss.week5.Zipper;

/**
 * Test program for Zipper.
 * Lab Exercise SoftwareSystems
 * @author Jip Spel
 * @version $Revision: 1.0 $
 */
public class ZipperTest {
    /**
     * Test for zipping with too few arguments
     */
    @Test
    public void testFewArguments() {
        assertThrows(TooFewArgumentsException.class, () -> {
            Zipper.zip2(null, "Hello World!");
        });
    }

    /**
     * Test for zipping with too few arguments
     */
    @Test
    public void testSecondArgumentNull() {
        assertThrows(TooFewArgumentsException.class, () -> {
            Zipper.zip2("Hello World!", null);
        });
    }

    /**
     * Test for zipping with arguments of different length
     */
    @Test
    public void testDifferentArgumentLengths() {
        assertThrows(ArgumentLengthsDifferException.class, () -> {
            Zipper.zip2("Hello World!", "Hello World");
        });
    }

    @Test
    public void testCorrectInput()
            throws TooFewArgumentsException, ArgumentLengthsDifferException {
        assertEquals("HelloWorld", Zipper.zip2("Hlool", "elWrd"));
    }
}
