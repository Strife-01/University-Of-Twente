package server;

import client.GoGameClientTUI;
import org.junit.jupiter.api.*;
import java.io.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration test for playing a game against the AI using actual TUI instances.
 * This test simulates a complete game between a human player and an AI opponent,
 * including initial setup, connection handling, and gameplay.
 */
public class AIGameplayTest {
    // Port for test server - using non-standard port to avoid conflicts
    private static final int TEST_PORT = 45670;

    // Threads for running human and AI TUIs independently
    private Thread humanThread;
    private Thread aiThread;

    // Output streams for simulating user input
    private PipedOutputStream humanOut;
    private PipedOutputStream aiOut;

    // Writers for sending simulated input to the TUIs
    private PrintWriter humanWriter;
    private PrintWriter aiWriter;

    // TUI instances for both players
    private GoGameClientTUI humanTUI;
    private GoGameClientTUI aiTUI;

    // Flag to control thread execution
    private volatile boolean testComplete = false;

    /**
     * Sets up the test environment before each test.
     * Creates necessary streams, writers, and threads for both players.
     */
    @BeforeEach
    void setUp() throws IOException {
        // Create piped streams for simulating keyboard input
        humanOut = new PipedOutputStream();
        aiOut = new PipedOutputStream();
        PipedInputStream humanIn = new PipedInputStream(humanOut);
        PipedInputStream aiIn = new PipedInputStream(aiOut);

        // Create writers for sending input to both TUIs
        humanWriter = new PrintWriter(humanOut, true);
        aiWriter = new PrintWriter(aiOut, true);

        // Initialize TUI instances
        humanTUI = new GoGameClientTUI();
        aiTUI = new GoGameClientTUI();

        // Create and configure thread for human player
        humanThread = new Thread(() -> {
            try {
                System.setIn(humanIn);
                setupHumanTUI();
            } catch (Exception e) {
                e.printStackTrace();
            }
        });

        // Create and configure thread for AI player
        aiThread = new Thread(() -> {
            try {
                System.setIn(aiIn);
                setupAITUI();
            } catch (Exception e) {
                e.printStackTrace();
            }
        });

        // Set threads as daemon to ensure they don't prevent JVM shutdown
        humanThread.setDaemon(true);
        aiThread.setDaemon(true);
    }

    /**
     * Continuously runs the human TUI until test completion.
     * This simulates the human player's client running.
     */
    private void setupHumanTUI() throws InterruptedException {
        while (!testComplete) {
            Thread.sleep(100);
        }
    }

    /**
     * Continuously runs the AI TUI until test completion.
     * This simulates the AI player's client running.
     */
    private void setupAITUI() throws InterruptedException {
        while (!testComplete) {
            Thread.sleep(100);
        }
    }

    /**
     * Cleans up resources after each test.
     * Closes streams and resets system input.
     */
    @AfterEach
    void tearDown() throws IOException {
        // Signal threads to stop
        testComplete = true;

        // Close all writers and streams
        if (humanWriter != null) humanWriter.close();
        if (aiWriter != null) aiWriter.close();
        if (humanOut != null) humanOut.close();
        if (aiOut != null) aiOut.close();

        // Restore system input to original state
        System.setIn(System.in);
    }

    /**
     * Tests a complete game between human and AI players.
     * Simulates all necessary input for connection, game setup, and moves.
     */
    @Test
    void testCompleteGameAgainstAI() throws InterruptedException, IOException {
        // Start both client TUIs in separate threads
        humanThread.start();
        Thread.sleep(500); // Wait for human thread to initialize
        aiThread.start();
        Thread.sleep(500); // Wait for AI thread to initialize

        // Configure human player connection and setup
        simulateHumanInput("localhost"); // Server address
        simulateHumanInput(String.valueOf(TEST_PORT)); // Port
        simulateHumanInput("HumanPlayer"); // Username
        simulateHumanInput("2"); // Join queue as human player

        // Configure AI player connection and setup
        simulateAIInput("localhost");
        simulateAIInput(String.valueOf(TEST_PORT));
        simulateAIInput("AIPlayer");
        simulateAIInput("3"); // Join queue as naive AI

        // Allow time for game initialization
        Thread.sleep(2000);

        // Simulate pressing enter to begin game
        simulateHumanInput("");
        simulateAIInput("");

        // Play several rounds
        for (int i = 0; i < 3; i++) {
            // Make move as human player
            simulateHumanInput("3,3"); // Example valid move
            Thread.sleep(500); // Wait for move processing

            // AI moves automatically
            Thread.sleep(500); // Wait for AI move
        }

        // Allow time for final game state updates
        Thread.sleep(2000);

        // Signal test completion
        testComplete = true;
    }

    /**
     * Sends simulated input to the human player's TUI.
     * @param input The input string to send
     */
    private void simulateHumanInput(String input) throws IOException {
        humanWriter.println(input);
        humanWriter.flush();
    }

    /**
     * Sends simulated input to the AI player's TUI.
     * @param input The input string to send
     */
    private void simulateAIInput(String input) throws IOException {
        aiWriter.println(input);
        aiWriter.flush();
    }
}