package client;

import client.protocol.ClientProtocol;
import game.implementations.Board;
import game.utils.Stone;
import java.awt.*;
import java.awt.event.KeyEvent;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.InetAddress;
import java.util.HashSet;
import java.util.Scanner;
import java.util.Set;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import network_abstractions.SocketConnection;

/**
 * The ClientConnection class manages communication between the client and the server.
 * It extends SocketConnection to handle messages received from the server and process game-related events.
 *
 * Responsibilities:
 * - Handles handshake and regular messages from the server.
 * - Manages game state based on server messages.
 * - Sends messages to the server.
 */
public class ClientConnection extends SocketConnection {
    private GoGameClient gameClient;

    //@ private invariant gameClient != null ==> gameClient.getHandshakeLock() != null;
    //@ private invariant gameClient != null ==> gameClient.getGameLock() != null;

    /**
     * Creates a new client connection to the given address and port.
     *
     * @param address The server's IP address.
     * @param port    The server's port.
     * @throws IOException If an I/O error occurs when creating the connection.
     */
    /*@ requires address != null && port > 0;
      @ ensures super.isConnected();
      @*/
    protected ClientConnection(InetAddress address, int port) throws IOException {
        super(address, port);
    }

    /**
     * Handles incoming messages from the server and processes them accordingly.
     *
     * @param message The message received from the server.
     */
    /*@ requires message != null;
      @*/
    @Override
    protected void handleMessage(String message) {
        if (message == null || message.isEmpty()) {
            return;
        }

        if (message.startsWith("ERROR")) {
            System.out.println(message.replaceFirst("ERROR~", ""));
            System.exit(-1);
        }

        if (gameClient.getSetUp() || gameClient.getSetUsername()) {
            handleHandshakeMessage(message);
            return;
        }

        handleRegularMessage(message);
    }

    /**
     * Handles handshake messages received from the server.
     *
     * @param message The handshake message.
     */
    /*@ requires message != null;
      @ ensures gameClient.getServerHandshakeResponse().equals(message);
      @*/
    private void handleHandshakeMessage(String message) {
        Lock handshakeLock = gameClient.getHandshakeLock();
        handshakeLock.lock();
        try {
            gameClient.setServerHandshakeResponse(message);
            gameClient.getHandshakeCondition().signal();
        } finally {
            handshakeLock.unlock();
        }
    }

    /**
     * Handles regular game-related messages from the server.
     *
     * @param message The message received.
     */
    /*@ requires message != null;
      @*/
    protected void handleRegularMessage(String message) {
        String[] components = message.split(ClientProtocol.SEPARATOR_ESCAPED.toString());
        if (components.length == 0) {
            return;
        }

        switch (components[0]) {
            case "NEWGAME":
                handleNewGame(components);
                break;
            case "MOVE":
                handleMove(components);
                break;
            case "GAMEOVER":
                handleGameOver(components);
                break;
            case "LIST":
                handleListPlayers(components);
                break;
            case "CHAT":
                handleChat(components);
                break;
            case "WHISPER":
                handleWhisper(components);
                break;
            case "CANNOTWHISPER":
                handleCannotWhisper(components);
                break;
            case "RANK":
                handleReceiveRanks(components);
                break;
            case "CHALLENGE":
                handleReceiveChallenge(components);
                break;
            case "REJECT":
                handleReceiveChallengeReject(components);
                break;
        }
    }

    /**
     * Processes a server message containing a list of players and prints the usernames.
     *
     * @param components An array of strings, where the first element contains the command type
     *                   and the subsequent elements contain the player usernames.
     */
    //@ requires components != null && components.length > 0;
    //@ ensures components.length == 1 ==> \result == null;
    //@ ensures components.length > 1 ==> (\forall int i; 1 <= i && i < components.length; components[i] != null);
    private void handleListPlayers(String[] components) {
        if (components.length == 1) {
            return;
        }

        System.out.println("\nThe players on the server are:");
        for (int i = 1; i < components.length; i++) {
            System.out.println("\t* " + components[i]);
        }
    }

    /**
     * Handles a "NEWGAME" message from the server.
     */
    /*@ requires components.length == 3;
      @ ensures gameClient.getIsPlayerInGame();
      @*/
    private void handleNewGame(String[] components) {
        if (components.length != 3) {
            return;
        }

        if (gameClient.getIsPlayerInChallengeQueue()) {
            gameClient.getChallengeLock().lock();
            gameClient.setIsPlayerInChallengeQueue(false);
            try {
                gameClient.setChallengeResponded(true);
                gameClient.setShowMenu(false);
                gameClient.setShowGame(true);
                gameClient.setIsPlayerQueued(true);
                gameClient.getChallengeCondition().signalAll();
            } catch (Exception e) {
                System.out.println("Challenge interrupted.");
            } finally {
                gameClient.getChallengeLock().unlock();
            }
        }

        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
            System.out.println("NewGame Interrupted");
        }

        gameClient.setIsPlayerQueued(true);
        gameClient.setIsPlayerInGame(true);
        gameClient.setCurrentGameBoard(new Board(Board.DIM));

        if (components[1].equals(gameClient.getUsername())) {
            gameClient.setIsPlayerTurn(true);
            gameClient.setPlayerStone(Stone.BLACK);
            gameClient.setOpponentName(components[2]);
        } else {
            gameClient.setIsPlayerTurn(false);
            gameClient.setPlayerStone(Stone.WHITE);
            gameClient.setOpponentName(components[1]);
        }

        System.out.println("\n\n\nNew game started between " + components[1] + " and " + components[2]);
        System.out.println("Press enter to begin.");
    }

    /**
     * Handles a "MOVE" message from the server.
     */
    /*@ requires components.length == 2;
      @ ensures gameClient.getReceivedMove() >= 0;
      @*/
    private void handleMove(String[] components) {
        if (components.length != 2) {
            return;
        }

        gameClient.getGameLock().lock();
        try {
            int movePosition = Integer.parseInt(components[1]);
            gameClient.setReceivedMove(movePosition);

            // Update board state
            if (!gameClient.getIsGameOver()) {
                Board currentBoard = gameClient.getCurrentGameBoard();

                if (!gameClient.getIsPlayerTurn()) {
                    // It's opponent's move, place their stone
                    Stone opponentStone = (gameClient.getPlayerStone() == Stone.BLACK) ? Stone.WHITE : Stone.BLACK;
                    if (currentBoard.isEmptyField(movePosition / Board.DIM, movePosition % Board.DIM)) {
                        currentBoard.setField(movePosition, opponentStone);
                    }
                }
            }

            // Signal that move has been processed
            gameClient.getGameCondition().signalAll();
        } catch (NumberFormatException e) {
            System.out.println("Invalid move received: " + components[1]);
        } finally {
            gameClient.getGameLock().unlock();
        }
    }


    /**
     * Handles the "GAMEOVER" message from the server.
     */
    /*@ requires components.length == 3;
      @ ensures gameClient.getIsGameOver();
      @*/
    private void handleGameOver(String[] components) {
        if (components.length != 3 || !(components[1].equals("VICTORY") || components[1].equals("DISCONNECT") || components[1].equals("DRAW"))) {
            return;
        }

        gameClient.getGameLock().lock();
        try {
            gameClient.setIsGameOver(true);
            gameClient.setWinner(components[2]);
            gameClient.setIsPlayerTurn(false);
            gameClient.getGameCondition().signalAll();
        } finally {
            gameClient.getGameLock().unlock();
        }
    }

    private void handleChat(String[] components) {
        if (components.length != 3) {
            return;
        }

        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
            System.out.println("The message tread was interrupted.");
        }

        System.out.println("\n" + components[1] + ": " + components[2]);
    }

    private void handleWhisper(String[] components) {
        if (components.length != 3) {
            return;
        }

        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
            System.out.println("The message tread was interrupted.");
        }

        System.out.println("\n" + components[1] + ": " + components[2]);
    }


    private void handleCannotWhisper(String[] components) {
        if (components.length != 2) {
            return;
        }

        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
            System.out.println("The message tread was interrupted.");
        }

        System.out.println("The player " + components[1] + "doesn't exist or doesn't support chat.");
    }

    private void handleReceiveRanks(String[] components) {
        if (components.length == 1 || components.length % 2 != 1) {
            return;
        }

        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
            System.out.println("The message tread was interrupted.");
        }

        System.out.println();

        int rankIndex = 1;

        for (int i = 1; i < components.length; i += 2) {
            System.out.println(rankIndex + ". " + components[i] + " with " + components[i + 1] + " wins.");
            rankIndex++;
        }
    }

    private void handleReceiveChallenge(String[] components) {
        if (components.length != 2) {
            return;
        }

        this.gameClient.setChallengerName(components[1]);
        this.gameClient.setShowChallenge(true);
        this.gameClient.setShowMenu(false);

        System.out.println("\n" + components[1] + " has challenged you to a game.");
        System.out.println("Please press enter to respond.");
    }

    private void handleReceiveChallengeReject(String[] components) {
        if (components.length != 2) {
            return;
        }

        System.out.println("The opponent rejected the challenge.");

        gameClient.getChallengeLock().lock();
        try {
            gameClient.getChallengeCondition().signalAll();
        } catch (Exception e) {
            System.out.println("The challenge has been interrupted");
        } finally {
            gameClient.getChallengeLock().unlock();
        }

        gameClient.setShowMenu(true);
        gameClient.setShowChallenge(false);
        gameClient.setShowGame(false);
        gameClient.setOpponentName(null);
        gameClient.setChallengeResponded(true);
    }

    /**
     * Handles client disconnection from the server.
     */
    @Override
    protected void handleDisconnect() {
        if (gameClient != null) {
            gameClient.handleDisconnect();
        }
    }


    /**
     * Sets the game client associated with this connection.
     */
    /*@ ensures this.gameClient == gameClient;
      @*/
    public void setGameClient(GoGameClient gameClient) {
        this.gameClient = gameClient;
    }

    /**
     * Sends the username to the server.
     */
    /*@ requires username != null;
      @*/
    public void sendUsername(String username) {
        String message = ClientProtocol.LOGIN.toString() +
                ClientProtocol.SEPARATOR +
                username;
        sendMessage(message);
    }

    /**
     * Sends a message to the server.
     */
    /*@ requires message != null;
      @*/
    public void sendServerMessage(String message) {
        sendMessage(message);
    }
}