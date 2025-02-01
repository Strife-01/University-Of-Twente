package server;

import game.interfaces.AbstractPlayer;
import game.interfaces.Game;
import java.io.IOException;
import java.net.Socket;
import network_abstractions.SocketConnection;
import server.protocol.ServerProtocol;

/**
 * ClientHandler is responsible for handling communication with a client,
 * managing game state, and interacting with other server components.
 * It processes messages, manages game state, and handles disconnections.
 */
public class ClientHandler extends SocketConnection {
    private ServerConnection serverConnection;
    private GoGameServer goGameServer;
    private String username = null;
    private boolean connected = false;
    private ClientHandler opponent = null;
    private Game currentGame = null;
    private AbstractPlayer thisPlayer = null;
    private boolean supportsChat = false;
    private boolean supportsRank = false;
    private boolean supportsNamedQueues = false;
    private boolean supportsChallenge = false;

    /**
     * Constructs a new `ClientHandler` with the specified socket connection.
     *
     * @param socket The socket connection to the client.
     * @throws IOException If an I/O error occurs while creating the connection.
     */
    /*@
        requires socket != null;
        ensures this.socket == socket;
    */
    public ClientHandler(Socket socket) throws IOException {
        super(socket);
    }

    public synchronized void setSupportsChallenge(boolean flag) {
        this.supportsChallenge = flag;
    }

    public synchronized boolean getSupportsChallenge() {
        return this.supportsChallenge;
    }

    public synchronized void setSupportsNamedQueues(boolean flag) {
        this.supportsNamedQueues = flag;
    }

    public synchronized boolean getSupportsNamedQueues() {
        return this.supportsNamedQueues;
    }

    public synchronized void setSupportsChat(boolean flag) {
        this.supportsChat = flag;
    }

    public synchronized boolean getSupportsChat() {
        return this.supportsChat;
    }

    public synchronized void setSupportsRank(boolean flag) {
        this.supportsRank = flag;
    }

    public synchronized boolean getSupportsRank() {
        return this.supportsRank;
    }

    /**
     * Sets the game server instance for this client handler.
     *
     * @param server The `GoGameServer` instance to associate with this client handler.
     */
    /*@
        requires server != null;
        ensures this.goGameServer == server;
    */
    public synchronized void setGoGameServer(GoGameServer server) {
        this.goGameServer = server;
    }

    /**
     * Returns the `AbstractPlayer` associated with this client handler.
     *
     * @return The `AbstractPlayer` instance representing this player.
     */
    /*@
        ensures \result == this.thisPlayer;
    */
    public synchronized AbstractPlayer getThisPlayer() {
        return this.thisPlayer;
    }

    /**
     * Sets the player associated with this client handler.
     *
     * @param player The `AbstractPlayer` instance representing the player.
     */
    /*@
        requires player != null;
        ensures this.thisPlayer == player;
    */
    public synchronized void setThisPlayer(AbstractPlayer player) {
        this.thisPlayer = player;
    }

    /**
     * Gets the current game that the client is participating in.
     *
     * @return The `Game` instance associated with the current game.
     */
    /*@
        ensures \result == this.currentGame;
    */

    public synchronized Game getCurrentGame() {
        return this.currentGame;
    }

    /**
     * Sets the current game associated with this client handler.
     *
     * @param newGame The `Game` instance representing the current game.
     */
    /*@
        requires newGame != null;
        ensures this.currentGame == newGame;
    */
    public synchronized void setCurrentGame(Game newGame) {
        this.currentGame = newGame;
    }

    /**
     * Sets the connection status for this client handler.
     *
     * @param flag The connection status (`true` for connected, `false` for disconnected).
     */
    /*@
        requires flag == true || flag == false;
        ensures this.connected == flag;
    */
    public void setConnected(boolean flag) {
        this.connected = flag;
    }

    /**
     * Checks if the client is connected to the server.
     *
     * @return `true` if the client is connected, `false` otherwise.
     */
    /*@
        ensures \result == this.connected;
    */
    public boolean getConnected() {
        return this.connected;
    }

    /**
     * Gets the opponent client handler.
     *
     * @return The `ClientHandler` instance representing the opponent.
     */
    /*@
        ensures \result == this.opponent;
    */
    public synchronized ClientHandler getOpponent() {
        return this.opponent;
    }

    /**
     * Sets the opponent for this client handler.
     *
     * @param opponent The `ClientHandler` instance representing the opponent.
     */
    /*@
        requires opponent != null;
        ensures this.opponent == opponent;
    */
    public synchronized void setOpponent(ClientHandler opponent) {
        this.opponent = opponent;
    }

    /**
     * Sets the server connection instance for this client handler.
     *
     * @param serverConnection The `ServerConnection` instance to associate with this client handler.
     */
    /*@
        requires serverConnection != null;
        ensures this.serverConnection == serverConnection;
    */
    public void setServerConnection(ServerConnection serverConnection) {
        this.serverConnection = serverConnection;
    }

    /**
     * Handles incoming messages and processes them based on the current game state.
     *
     * @param message The message received from the client.
     */
    /*@
        requires message != null;
        ensures this.username != null;
        ensures (\old(this.username) == null) || (this.username.equals(\old(this.username)));
    */
    @Override
    public synchronized void handleMessage(String message) {
        if (username != null) {
            System.out.println(username + ": " + message);
            goGameServer.handleChatMessage(this, message);
        }
    }

    /**
     * Sends a server message to the client.
     *
     * @param username The username of the player receiving the message.
     * @param message  The message to send to the client.
     */
    /*@
        requires username != null && message != null;
        ensures this.serverConnection != null;
    */
    public void sendServerMessage(String username, String message) {
        if (serverConnection != null) {
            serverConnection.sendServerMessage(message);
        }
    }

    /**
     * Handles the disconnection of the client, notifies the opponent, and cleans up the game state.
     */
    /*@
        ensures !this.connected;
        ensures opponent.getConnected() == false;
        ensures this.currentGame == null;
    */
    @Override
    public synchronized void handleDisconnect() {
        if (username != null) {
            System.out.println(username + " has left the game room.");
        }
        if (opponent != null && currentGame != null) {
            try {
                Thread.sleep(200);
            } catch (InterruptedException e) {
                System.out.println("The thread has been killed.");
            }
            opponent.sendServerMessage(opponent.getUsername(), ServerProtocol.GAMEOVER.toString()
                    + ServerProtocol.SEPARATOR
                    + ServerProtocol.DISCONNECT
                    + ServerProtocol.SEPARATOR
                    + opponent.getUsername());
            goGameServer.incrementWins(opponent.getUsername());

            // Clean up game state
            serverConnection.cleanupGame(this, opponent);
        }
        goGameServer.removeClient(this);
    }

    /**
     * Sets the username for the client.
     *
     * @param username The username to associate with this client handler.
     */
    /*@
        requires username != null;
        ensures this.username == username;
    */
    public synchronized void receiveUsername(String username) {
        if (this.username == null) {
            this.username = username;
            System.out.println("Username set to: " + username);
        }
    }

    /**
     * Gets the username of the client.
     *
     * @return The username associated with this client handler.
     */
    /*@
        ensures \result != null;
    */
    public String getUsername() {
        return username;
    }
}
