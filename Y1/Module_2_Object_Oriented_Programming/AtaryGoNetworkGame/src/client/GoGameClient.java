package client;

import client.ClientConnection;
import client.ClientListener;
import client.protocol.ClientProtocol;
import game.implementations.Board;
import game.utils.Stone;
import java.io.IOException;
import java.net.InetAddress;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * The GoGameClient class represents the client-side logic of a Go game.
 * It handles server communication, game state management, and user interactions.
 *
 * Responsibilities:
 * - Manages connection to the server.
 * - Handles handshake and game-related messages.
 * - Tracks game state, including players, turns, and moves.
 * - Allows for client-side event handling and interaction with listeners.
 */
public class GoGameClient {
    private final ClientConnection connection;
    private final Set<ClientListener> listeners;

    private final Lock handshakeLock;
    private final Condition handshakeCondition;
    private final Lock gameLock;
    private final Condition gameCondition;
    private final Lock challengeLock;
    private final Condition challengeCondition;

    private boolean isSetUp;
    private boolean isSetUsername;
    private String serverHandshakeResponse;
    private String username;
    private String opponentName;
    private String challengerName;
    private boolean challengeResponded = false;

    private boolean showMenu;
    private boolean showGame;
    private boolean showChallenge;
    private boolean isPlayerQueued;
    private boolean isPlayerInGame;
    private boolean isPlayerInChallengeQueue;
    private Stone playerStone;
    private boolean isPlayerTurn;
    private boolean isGameOver;
    private String winner;

    private Board currentGameBoard;
    private int receivedMove;

    /**
     * Constructs a GoGameClient instance, establishing a connection with the server.
     *
     * @param address The server's IP address.
     * @param port The server's port number.
     * @throws IOException If an I/O error occurs during connection setup.
     */
    //@ requires address != null && port > 0;
    //@ ensures connection != null && connection.isConnected();
    public GoGameClient(InetAddress address, int port) throws IOException {
        try {
            this.connection = new ClientConnection(address, port);
            this.connection.setGameClient(this);
            this.listeners = new HashSet<>();

            this.handshakeLock = new ReentrantLock();
            this.handshakeCondition = handshakeLock.newCondition();
            this.gameLock = new ReentrantLock();
            this.gameCondition = gameLock.newCondition();
            this.challengeLock = new ReentrantLock();
            this.challengeCondition = challengeLock.newCondition();

            this.isSetUp = true;
            this.isSetUsername = true;
            this.serverHandshakeResponse = null;

            this.showMenu = true;
            this.challengerName = null;
            this.showChallenge = false;
            this.isPlayerQueued = false;
            this.isPlayerInGame = false;
            this.isGameOver = false;
            this.winner = null;

            this.currentGameBoard = null;
            this.receivedMove = -1;
        } catch (IOException e) {
            throw new IOException("Failed to create client connection: " + e.getMessage());
        }
    }

    public synchronized void setIsPlayerInChallengeQueue(boolean flag) {
        this.isPlayerInChallengeQueue = flag;
    }

    public synchronized boolean getIsPlayerInChallengeQueue() {
        return this.isPlayerInChallengeQueue;
    }

    public synchronized void setChallengeResponded(boolean flag) {
        this.challengeResponded = flag;
    }

    public synchronized boolean getChallengeResponded() {
        return this.challengeResponded;
    }

    public synchronized void setChallengerName(String name) {
        this.challengerName = name;
    }

    public synchronized String getChallengerName() {
        return this.challengerName;
    }

    public synchronized void setShowChallenge(boolean flag) {
        this.showChallenge = flag;
    }

    public synchronized boolean getShowChallenge() {
        return this.showChallenge;
    }

    public synchronized Lock getChallengeLock() {
        return this.challengeLock;
    }

    public synchronized Condition getChallengeCondition() {
        return this.challengeCondition;
    }

    /**
     * Sets the name of the opponent player.
     *
     * @param name The name of the opponent.
     */
    //@ requires name != null && !name.isEmpty();
    //@ ensures opponentName != null && opponentName.equals(name);
    public synchronized void setOpponentName(String name) {
        this.opponentName = name;
    }

    /**
     * Retrieves the name of the opponent player.
     *
     * @return The opponent's name.
     */
    //@ ensures \result != null;
    public synchronized String getOpponentName() {
        return this.opponentName;
    }

    /**
     * Retrieves the lock used for the handshake process.
     *
     * @return The handshake lock.
     */
    //@ ensures \result != null;
    public Lock getHandshakeLock() {
        return handshakeLock;
    }

    /**
     * Retrieves the condition associated with the handshake process.
     *
     * @return The handshake condition.
     */
    //@ ensures \result != null;
    public Condition getHandshakeCondition() {
        return handshakeCondition;
    }

    /**
     * Retrieves the lock used for game-related synchronization.
     *
     * @return The game lock.
     */
    //@ ensures \result != null;
    public Lock getGameLock() {
        return gameLock;
    }

    /**
     * Retrieves the condition associated with game synchronization.
     *
     * @return The game condition.
     */
    //@ ensures \result != null;
    public Condition getGameCondition() {
        return gameCondition;
    }

    /**
     * Checks if the game is over.
     *
     * @return True if the game is over, otherwise false.
     */
    //@ ensures \result == isGameOver;
    public synchronized boolean getIsGameOver() {
        return isGameOver;
    }

    /**
     * Sets the game-over flag.
     *
     * @param flag The value to set for the game-over flag.
     */
    //@ requires flag == true || flag == false;
    //@ ensures isGameOver == flag;
    public synchronized void setIsGameOver(boolean flag) {
        this.isGameOver = flag;
    }

    /**
     * Retrieves the winner of the game.
     *
     * @return The winner's username, or null if there is no winner yet.
     */
    //@ ensures \result == winner;
    public synchronized String getWinner() {
        return winner;
    }

    /**
     * Sets the winner of the game.
     *
     * @param username The username of the winner.
     */
    //@ requires username != null && !username.isEmpty();
    //@ ensures winner != null && winner.equals(username);
    public synchronized void setWinner(String username) {
        this.winner = username;
    }

    /**
     * Checks if the setup process is complete.
     *
     * @return True if setup is complete, otherwise false.
     */
    //@ ensures \result == isSetUp;
    public synchronized boolean getSetUp() {
        return isSetUp;
    }

    /**
     * Sets the setup status.
     *
     * @param flag The setup status to set.
     */
    //@ requires flag == true || flag == false;
    //@ ensures isSetUp == flag;
    public synchronized void setSetUp(boolean flag) {
        this.isSetUp = flag;
    }

    /**
     * Checks if the username has been set.
     *
     * @return True if the username is set, otherwise false.
     */
    //@ ensures \result == isSetUsername;
    public synchronized boolean getSetUsername() {
        return isSetUsername;
    }

    /**
     * Sets the username status.
     *
     * @param flag The username status to set.
     */
    //@ requires flag == true || flag == false;
    //@ ensures isSetUsername == flag;
    public synchronized void setSetUsername(boolean flag) {
        this.isSetUsername = flag;
    }

    /**
     * Retrieves the server handshake response.
     *
     * @return The handshake response from the server.
     */
    //@ ensures \result == serverHandshakeResponse;
    public synchronized String getServerHandshakeResponse() {
        return serverHandshakeResponse;
    }


    /**
     * Sets the server handshake response.
     *
     * @param response The server handshake response.
     */
    //@ requires response != null && !response.isEmpty();
    //@ ensures serverHandshakeResponse != null && serverHandshakeResponse.equals(response);
    public synchronized void setServerHandshakeResponse(String response) {
        this.serverHandshakeResponse = response;
    }

    /**
     * Retrieves the current username of the client.
     *
     * @return The username of the client.
     */
    //@ ensures \result == username;
    public synchronized String getUsername() {
        return username;
    }

    /**
     * Sets the current username of the client.
     *
     * @param username The username to set.
     */
    //@ requires username != null && !username.isEmpty();
    //@ ensures username != null && username.equals(username);
    public synchronized void setUsername(String username) {
        this.username = username;
    }

    /**
     * Checks if the menu should be displayed.
     *
     * @return True if the menu should be displayed, otherwise false.
     */
    //@ ensures \result == showMenu;
    public synchronized boolean getShowMenu() {
        return showMenu;
    }

    /**
     * Sets the display status for the menu.
     *
     * @param flag The flag indicating whether to show the menu.
     */
    //@ requires flag == true || flag == false;
    //@ ensures showMenu == flag;
    public synchronized void setShowMenu(boolean flag) {
        this.showMenu = flag;
    }

    /**
     * Checks if the game view should be displayed.
     *
     * @return True if the game view should be displayed, otherwise false.
     */
    //@ ensures \result == showGame;
    public synchronized boolean getShowGame() {
        return this.showGame;
    }

    /**
     * Sets the display status for the game view.
     *
     * @param flag The flag indicating whether to show the game view.
     */
    //@ requires flag == true || flag == false;
    //@ ensures showGame == flag;
    public synchronized void setShowGame(boolean flag) {
        this.showGame = flag;
    }

    /**
     * Checks if the player is currently queued for a game.
     *
     * @return True if the player is queued, otherwise false.
     */
    //@ ensures \result == isPlayerQueued;
    public synchronized boolean getIsPlayerQueued() {
        return isPlayerQueued;
    }

    /**
     * Sets the player's queue status.
     *
     * @param flag The flag indicating whether the player is queued.
     */
    //@ requires flag == true || flag == false;
    //@ ensures isPlayerQueued == flag;
    public synchronized void setIsPlayerQueued(boolean flag) {
        this.isPlayerQueued = flag;
    }

    /**
     * Checks if the player is currently in a game.
     *
     * @return True if the player is in a game, otherwise false.
     */
    //@ ensures \result == isPlayerInGame;
    public synchronized boolean getIsPlayerInGame() {
        return isPlayerInGame;
    }

    /**
     * Sets the player's in-game status.
     *
     * @param flag The flag indicating whether the player is in a game.
     */
    //@ requires flag == true || flag == false;
    //@ ensures isPlayerInGame == flag;
    public synchronized void setIsPlayerInGame(boolean flag) {
        this.isPlayerInGame = flag;
    }

    /**
     * Retrieves the player's stone type (black or white).
     *
     * @return The stone type of the player.
     */
    //@ ensures \result == playerStone;
    public synchronized Stone getPlayerStone() {
        return playerStone;
    }

    /**
     * Sets the player's stone type (black or white).
     *
     * @param stone The stone type to set for the player.
     */
    //@ requires stone != null;
    //@ ensures playerStone != null && playerStone.equals(stone);
    public synchronized void setPlayerStone(Stone stone) {
        this.playerStone = stone;
    }

    /**
     * Checks if it is the player's turn.
     *
     * @return True if it is the player's turn, otherwise false.
     */
    //@ ensures \result == isPlayerTurn;
    public synchronized boolean getIsPlayerTurn() {
        return isPlayerTurn;
    }

    /**
     * Sets the player's turn status.
     *
     * @param flag The flag indicating whether it is the player's turn.
     */
    //@ requires flag == true || flag == false;
    //@ ensures isPlayerTurn == flag;
    public synchronized void setIsPlayerTurn(boolean flag) {
        this.isPlayerTurn = flag;
    }

    /**
     * Retrieves the current game board.
     *
     * @return The current game board.
     */
    //@ ensures \result == currentGameBoard;
    public synchronized Board getCurrentGameBoard() {
        return currentGameBoard;
    }

    /**
     * Sets the current game board.
     *
     * @param board The board to set for the current game.
     */
    //@ requires board != null;
    //@ ensures currentGameBoard != null && currentGameBoard.equals(board);
    public synchronized void setCurrentGameBoard(Board board) {
        this.currentGameBoard = board;
    }

    /**
     * Retrieves the last received move.
     *
     * @return The position of the last received move.
     */
    //@ ensures \result == receivedMove;
    public synchronized int getReceivedMove() {
        return receivedMove;
    }

    /**
     * Sets the last received move.
     *
     * @param move The position of the move.
     */
    //@ requires move >= 0;
    //@ ensures receivedMove == move;
    public synchronized void setReceivedMove(int move) {
        this.receivedMove = move;
    }

    /**
     * Resets the game state to prepare for a new game.
     * This method clears game-specific flags, board, and player information.
     */
    //@ ensures isGameOver == false && winner == null && currentGameBoard == null && isPlayerInGame == false;
    public void resetGame() {
        setIsGameOver(false);
        setWinner(null);
        setCurrentGameBoard(null);
        setIsPlayerInGame(false);
        setIsPlayerQueued(false);
        setShowGame(false);
        setShowMenu(true);
        setOpponentName(null);
    }

    /**
     * Sends a move to the server with the specified position.
     *
     * @param position The position of the move on the board.
     */
    //@ requires position >= 0;
    //@ ensures receivedMove == position;
    public void sendMove(int position) {
        String message = ClientProtocol.MOVE.toString() + ClientProtocol.SEPARATOR + position;
        connection.sendServerMessage(message);
    }

    /**
     * Closes the connection to the server.
     */
    public void close() {
        System.out.println("Closing connection to server...");
        connection.close();
        System.out.println("Connection closed.");
    }

    /**
     * Handles the event when the connection is lost.
     */
    public synchronized void handleDisconnect() {
        for (ClientListener listener : listeners) {
            listener.connectionLost();
        }
    }

    /**
     * Adds a listener to the client for handling events.
     *
     * @param listener The listener to add.
     */
    public synchronized void addListener(ClientListener listener) {
        listeners.add(listener);
    }

    /**
     * Removes a listener from the client.
     *
     * @param listener The listener to remove.
     */
    public synchronized void removeListener(ClientListener listener) {
        listeners.remove(listener);
    }

    /**
     * Retrieves the client connection instance.
     *
     * @return The client connection.
     */
    //@ ensures \result != null;
    public ClientConnection getConnection() {
        return connection;
    }

    /**
     * Sends the username to the server.
     *
     * @param username The username to send.
     */
    public void sendUsername(String username) {
        connection.sendUsername(username);
    }

    /**
     * Sends a message to the server.
     *
     * @param message The message to send.
     */
    public void sendServerMessage(String message) {
        connection.sendServerMessage(message);
    }
}