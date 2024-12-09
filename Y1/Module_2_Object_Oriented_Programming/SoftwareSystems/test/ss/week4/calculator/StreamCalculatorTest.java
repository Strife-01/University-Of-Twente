package ss.week4.calculator;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.week4.calculator.reference.MyCalculator;
import ss.week4.calculator.reference.MyStreamCalculator;

import java.io.*;
import java.util.concurrent.Semaphore;
import ss.week4.calculator.StreamCalculator;

import static org.junit.jupiter.api.Assertions.*;


class StreamCalculatorTest {
    private static StreamCalculator streamCalculator;

    @BeforeEach
    void setup() {
        // Create a new StreamCalculator before each test
        streamCalculator = new MyStreamCalculator(); // FIXME replace with the actual calculator
    }

    /**
     * Simple test if the stream calculator can do some basic operations
     */
    @Test
    void fileAndStringTest() throws IOException {
        try (var fr = new FileReader("src/ss/week4/calculator/reference/calculatorinstructions")) {
            // stringwriter! Basically writes to a string
            var sw = new StringWriter();
            streamCalculator.process(fr, sw);
            // after we get the string, we just use a stringreader around the string :-)
            // an alternative is to use piped streams
            try (var br = new BufferedReader(new StringReader(sw.toString()))) {
                assertEquals("-120.0", br.readLine());
                assertEquals("34.5", br.readLine());
                assertEquals("400.0", br.readLine());
                assertEquals("0.025", br.readLine());
            }
        }
    }

    /**
     * Utility class to help detect whether a stream is properly flushed.
     *
     * The idea is that the test method calls waitUntilRead(), which will not return until the reading thread
     * has finished reading from the delegate.
     * Once this is done, the reading thread will halt until released by the test method via releaseReader()
     */
    private static class HaltingReader extends Reader {
        private final Reader delegate;
        private final Semaphore s1 = new Semaphore(0);
        private final Semaphore s2 = new Semaphore(0);

        public HaltingReader(Reader delegate) {
            this.delegate = delegate;
        }

        /**
         * Returns after all characters are read by the reading thread
         */
        public void waitUntilRead() {
            try {
                s1.acquire();
                s1.release(); // in case waitUntilRead is called multiple times...
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }

        /**
         * Allow the reader to finish
         */
        public void releaseReader() {
            s2.release();
        }

        /**
         * Read from the stream. This is delegated to the provided Reader object. When the Reader reaches the end
         * of stream, this method will release the semaphore allowing waitUntilRead to return
         */
        @Override
        public int read(char[] cbuf, int off, int len) throws IOException {
            var res = delegate.read(cbuf, off, len);
            if (res == -1) {
                try {
                    s1.release();
                    s2.acquire();
                } catch (InterruptedException e) {
                    // we just bounce the interrupt further
                    Thread.currentThread().interrupt();
                }
            }
            return res;
        }

        @Override
        public boolean ready() throws IOException {
            return delegate.ready();
        }

        @Override
        public void close() throws IOException {
            delegate.close();
        }
    }

    @Test
    void testIfFlushes() throws IOException, InterruptedException {
        try (final var sr = new StringReader("push 12\npop\n");
             final var hr = new HaltingReader(sr);
             final var wr = new CharArrayWriter();
             final var bw = new BufferedWriter(wr)) {
            // create a thread and run the calculator on the prepared streams
            var testThread = new Thread(() -> streamCalculator.process(hr, bw));
            testThread.start();

            // now let the stream calculator read until end of input, then wait using the semaphore
            hr.waitUntilRead();

            // if this fails, then you forgot to flush after writing the result!
            // the problem with that is that nothing is really written through a BufferedWriter until you flush.
            //assertNotEquals("", wr.toString().trim(), "Please flush after writing to the stream!");

            // if this fails, then you simply didn't compute the correct answer!
            //assertEquals("12.0", wr.toString().trim(), "Incorrect value sent to the stream!");

            // finally, we can release the reading thread and wait for it to be finished...
            hr.releaseReader();
            testThread.join();
        }
    }

    /**
     * Test if the streamCalculator handles a closed output stream
     */
    @Test
    void closedWriterTest() throws IOException {
        // Here we use a try-with-resources block...
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var pw = new PrintWriter(pw1)) {
            pw.println("push 1");
            pw.println("push 0");
            pw.println("div");
            pw.println("pop");
            pw.close();
            pr2.close();
            pw2.close();
            // the output streams are closed. what will happen? (the process method should not crash/stacktrace)
            streamCalculator.process(pr1, pw2);
        }
    }

    /**
     * Test if a bad push syntax results in an error message
     */
    @Test
    void invalidPushTest() throws IOException {
        // Here we use a try-with-resources block...
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var br = new BufferedReader(pr2); var pw = new PrintWriter(pw1)) {
            pw.println("push"); // this is a bug. push should have a parameter
            pw.println("push 0");
            pw.println("add");
            pw.println("pop");
            pw.close();
            // if this method call crashes, then push is not checked properly
            streamCalculator.process(pr1, pw2);
            String s = br.readLine();
            assertNotNull(s);
            assertTrue(s.startsWith("error: "));
        }
    }

    /**
     * Test if an empty line results in an error message
     */
    @Test
    void emptyLineTest() throws IOException {
        // Here we use a try-with-resources block...
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var br = new BufferedReader(pr2); var pw = new PrintWriter(pw1)) {
            pw.println("push 1");
            pw.println("push 0");
            pw.println(""); // this is an invalid command, should report an error
            pw.println("pop");
            pw.close();
            // if this method call crashes, then push is not checked properly
            streamCalculator.process(pr1, pw2);
            String s = br.readLine();
            assertNotNull(s);
            assertTrue(s.startsWith("error: "));
        }
    }

    /**
     * Test if an invalid command results in an error message
     */
    @Test
    void invalidCommandTest() throws IOException {
        // Here we use a try-with-resources block...
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var br = new BufferedReader(pr2); var pw = new PrintWriter(pw1)) {
            pw.println("push 1");
            pw.println("push 0");
            pw.println("blablabla"); // this is an invalid command, should report an error
            pw.println("pop");
            pw.close();
            // if this method call crashes, then push is not checked properly
            streamCalculator.process(pr1, pw2);
            String s = br.readLine();
            assertNotNull(s);
            assertTrue(s.startsWith("error: "));
        }
    }

    /**
     * Test if a divide by zero results in an error message
     */
    @Test
    void divideByZeroTest() throws IOException {
        // Here we use a try-with-resources block...
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var br = new BufferedReader(pr2); var pw = new PrintWriter(pw1)) {
            pw.println("push 1");
            pw.println("push 0");
            pw.println("div");
            pw.println("pop");
            pw.close();
            streamCalculator.process(pr1, pw2);
            String s = br.readLine();
            assertNotNull(s);
            assertTrue(s.startsWith("error: "));
        }
    }

    /**
     * Test if pop() on an empty stack results in an error message
     */
    @Test
    void emptyStackTestPop() throws IOException {
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var br = new BufferedReader(pr2); var pw = new PrintWriter(pw1)) {
            pw.println("push 1");
            pw.println("push 0");
            pw.println("pop");
            pw.println("pop");
            pw.println("pop");
            pw.close();
            streamCalculator.process(pr1, pw2);
            String s = br.readLine();
            assertNotNull(s);
            assertEquals("0.0", s);
            s = br.readLine();
            assertNotNull(s);
            assertEquals("1.0", s);
            s = br.readLine();
            assertNotNull(s);
            assertTrue(s.startsWith("error: "));
        }
    }

    /**
     * Test if add() on an empty stack results in an error message
     */
    @Test
    void emptyStackTestAdd() throws IOException {
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var br = new BufferedReader(pr2); var pw = new PrintWriter(pw1)) {
            pw.println("push 1.5");
            pw.println("push 0.5");
            pw.println("add");
            pw.println("pop");
            pw.println("push 0");
            pw.println("add");
            pw.close();
            streamCalculator.process(pr1, pw2);
            String s = br.readLine();
            assertNotNull(s);
            assertEquals("2.0", s);
            s = br.readLine();
            assertNotNull(s);
            assertTrue(s.startsWith("error: "));
        }
    }

    /**
     * Test if sub() on an empty stack results in an error message
     */
    @Test
    void emptyStackTestSub() throws IOException {
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var br = new BufferedReader(pr2); var pw = new PrintWriter(pw1)) {
            pw.println("push 1.5");
            pw.println("push 0.5");
            pw.println("sub");
            pw.println("pop");
            pw.println("push 0");
            pw.println("sub");
            pw.close();
            streamCalculator.process(pr1, pw2);
            String s = br.readLine();
            assertNotNull(s);
            assertEquals("1.0", s);
            s = br.readLine();
            assertNotNull(s);
            assertTrue(s.startsWith("error: "));
        }
    }

    /**
     * Test if mult() on an empty stack results in an error message
     */
    @Test
    void emptyStackTestMult() throws IOException {
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var br = new BufferedReader(pr2); var pw = new PrintWriter(pw1)) {
            pw.println("push 1.5");
            pw.println("push 0.5");
            pw.println("mult");
            pw.println("pop");
            pw.println("push 0");
            pw.println("mult");
            pw.close();
            streamCalculator.process(pr1, pw2);
            String s = br.readLine();
            assertNotNull(s);
            assertEquals("0.75", s);
            s = br.readLine();
            assertNotNull(s);
            assertTrue(s.startsWith("error: "));
        }
    }

    /**
     * Test if div() on an empty stack results in an error message
     */
    @Test
    void emptyStackTestDiv() throws IOException {
        try (var pr1 = new PipedReader(); var pw1 = new PipedWriter(pr1);
             var pr2 = new PipedReader(); var pw2 = new PipedWriter(pr2);
             var br = new BufferedReader(pr2); var pw = new PrintWriter(pw1)) {
            pw.println("push 1.5");
            pw.println("push 0.5");
            pw.println("div");
            pw.println("pop");
            pw.println("push 0");
            pw.println("div");
            pw.close();
            streamCalculator.process(pr1, pw2);
            String s = br.readLine();
            assertNotNull(s);
            assertEquals("3.0", s);
            s = br.readLine();
            assertNotNull(s);
            assertTrue(s.startsWith("error: "));
        }
    }

    /**
     * Combined test of features of the streaming calculator
     */
    @Test
    void combinedFeaturesTest() throws IOException, InterruptedException {
        try (final var pr = new PipedReader();
             final var pw = new PrintWriter(new PipedWriter(pr));
             final var wr = new CharArrayWriter();
             final var bw = new BufferedWriter(wr)) {
            var t = new Thread(() -> streamCalculator.process(pr, bw));

            t.start();
            pw.println("push 12");
            pw.println("push 0");
            pw.println("div");
            pw.println("pop");
            pw.println("pop");
            pw.close();
            t.join();

            try (var br = new BufferedReader(new StringReader(wr.toString()))) {
                String line;
                assertTrue((line = br.readLine()) != null && line.startsWith("error: ")); // divide by zero
                assertEquals("NaN", br.readLine()); // result of divide by zero
                assertTrue((line = br.readLine()) != null && line.startsWith("error: ")); // error stack empty
                assertNull(br.readLine());
            }
        }
    }
}
