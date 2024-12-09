package ss.week4.calculator;

import java.io.IOException;
import java.io.Reader;
import java.io.Writer;

/**
 * A stream wrapper around the calculator that reads commands from the given Reader and writes output to the Writer
 * Each command is a single line, for example:
 * - "push 100.5"
 * - "pop"
 * - "add"
 * - "sub"
 * - "mult"
 * - "div"
 * After a pop, the obtained value is written on a single line to the output.
 * If there is an error, a line is written starting with "error: " followed by an error message
 */
public interface StreamCalculator {
    /**
     * Process all commands read from the given input, and write the result(s) to the given output
     * @param input the Reader to read commands from
     * @param output the Writer to write output to
     */
    void process(Reader input, Writer output);
}
