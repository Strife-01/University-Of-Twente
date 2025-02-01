package server;

import client.GoGameClient;
import game.implementations.Board;
import org.junit.jupiter.api.*;
import static org.junit.jupiter.api.Assertions.*;
import java.io.IOException;
import java.net.InetAddress;
import java.util.ArrayList;
import java.util.List;
import client.protocol.ClientProtocol;
import server.protocol.ServerProtocol;

/**
 * Test suite for handling network errors and edge cases in the Go game
 * client-server implementation.
 */
public class GoGameNetworkTest {
    private static GoGameServer server;
    private static final int TEST_PORT = 8890;
    private static final String TEST_HOST = "localhost";

    @BeforeEach
    void setUp() throws IOException {
        server = new GoGameServer(TEST_PORT);
        new Thread(() -> {
            try {
                server.acceptConnections();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }).start();

        // Wait for server startup
        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    @AfterEach
    void tearDown() {
        if (server != null) {
            server.close();
        }
    }

    /**
     * Tests error handling during client connection setup
     */
    @Test
    void testConnectionSetupErrors() throws IOException, InterruptedException {
        // Test connection with valid setup
        GoGameClient client = new GoGameClient(InetAddress.getByName(TEST_HOST), TEST_PORT);
        assertTrue(client.getSetUp()); // Check if client is properly set up

        client.close();
    }

    /**
     * Tests handling of protocol message errors
     */
    @Test
    void testProtocolMessageErrors() throws IOException, InterruptedException {
        GoGameClient client = new GoGameClient(InetAddress.getByName(TEST_HOST), TEST_PORT);
        client.setSetUsername(true);
        client.setUsername("TestPlayer");

        // Send invalid/malformed messages
        client.sendServerMessage("INVALID" + ServerProtocol.SEPARATOR + "MESSAGE");
        client.sendServerMessage("MOVE" + ServerProtocol.SEPARATOR + "-1"); // Invalid move
        client.sendServerMessage("QUEUE" + ServerProtocol.SEPARATOR + "EXTRA"); // Malformed queue message

        // Verify client hasn't disconnected (would be indicated by game over state)
        assertFalse(client.getIsGameOver());

        client.close();
    }

    /**
     * Tests handling of multiple client connections and disconnections
     */
    @Test
    void testMultipleClientHandling() throws IOException, InterruptedException {
        List<GoGameClient> clients = new ArrayList<>();

        // Create multiple clients
        for (int i = 0; i < 5; i++) {
            GoGameClient client = new GoGameClient(InetAddress.getByName(TEST_HOST), TEST_PORT);
            client.setUsername("Player" + i);
            clients.add(client);

            // Verify each client is properly set up
            assertTrue(client.getSetUp());
        }

        // Disconnect clients in sequence
        for (GoGameClient client : clients) {
            client.close();
            Thread.sleep(100); // Brief pause between disconnections
        }

        // Verify server remains operational by connecting a new client
        GoGameClient finalClient = new GoGameClient(InetAddress.getByName(TEST_HOST), TEST_PORT);
        assertTrue(finalClient.getSetUp());
        finalClient.close();
    }

    /**
     * Tests game state handling during unexpected disconnections
     */
    @Test
    void testGameStateOnDisconnection() throws IOException, InterruptedException {
        GoGameClient client1 = new GoGameClient(InetAddress.getByName(TEST_HOST), TEST_PORT);
        GoGameClient client2 = new GoGameClient(InetAddress.getByName(TEST_HOST), TEST_PORT);

        // Set up clients
        client1.setSetUsername(true);
        client2.setSetUsername(true);
        client1.setUsername("Player1");
        client2.setUsername("Player2");

        // Start a game
        client1.setIsPlayerQueued(true);
        client2.setIsPlayerQueued(true);
        client1.sendServerMessage(ClientProtocol.QUEUE.toString());
        client2.sendServerMessage(ClientProtocol.QUEUE.toString());

        Thread.sleep(1000); // Wait for game to start

        // Simulate unexpected disconnection
        client1.close();
        Thread.sleep(1000);

        // Verify client2's game state is handled appropriately
        assertTrue(client2.getIsGameOver() || !client2.getIsPlayerInGame());

        client2.close();
    }

    /**
     * Tests server response to invalid move sequences
     */
    @Test
    void testInvalidMoveSequences() throws IOException, InterruptedException {
        GoGameClient client1 = new GoGameClient(InetAddress.getByName(TEST_HOST), TEST_PORT);
        GoGameClient client2 = new GoGameClient(InetAddress.getByName(TEST_HOST), TEST_PORT);

        // Set up clients
        client1.setSetUsername(true);
        client2.setSetUsername(true);
        client1.setUsername("Player1");
        client2.setUsername("Player2");

        // Queue for game
        client1.setIsPlayerQueued(true);
        client2.setIsPlayerQueued(true);
        client1.sendServerMessage(ClientProtocol.QUEUE.toString());
        client2.sendServerMessage(ClientProtocol.QUEUE.toString());

        Thread.sleep(1000); // Wait for game to start

        // Attempt invalid moves
        if (!client1.getIsPlayerTurn()) {
            client1.sendMove(0); // Move out of turn
        }
        client1.sendMove(-1); // Invalid position
        client1.sendMove(Board.DIM * Board.DIM); // Out of bounds

        client1.close();
        client2.close();
    }

    /**
     * Tests handling of rapid queue join/leave operations
     */
    @Test
    void testQueueOperations() throws IOException, InterruptedException {
        GoGameClient client = new GoGameClient(InetAddress.getByName(TEST_HOST), TEST_PORT);
        client.setUsername("QueueTester");

        // Rapidly join and leave queue
        for (int i = 0; i < 5; i++) {
            client.setIsPlayerQueued(true);
            client.sendServerMessage(ClientProtocol.QUEUE.toString()); // Join
            Thread.sleep(100);
            client.setIsPlayerQueued(false);
            client.sendServerMessage(ClientProtocol.QUEUE.toString()); // Leave
            Thread.sleep(100);
        }

        // Verify client remains in valid state
        assertFalse(client.getIsPlayerInGame());
        assertFalse(client.getIsPlayerQueued());

        client.close();
    }
}