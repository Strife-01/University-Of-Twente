package server;

import game.implementations.GoGame;
import game.implementations.GoMove;
import game.implementations.HumanPlayer;
import game.interfaces.AbstractPlayer;
import game.interfaces.Game;
import game.interfaces.Move;
import game.interfaces.Player;
import game.utils.Stone;
import java.io.IOException;
import java.net.Socket;
import java.util.*;
import java.util.stream.Collectors;
import network_abstractions.SocketConnection;
import server.protocol.ServerProtocol;

/**
 * This class manages communication between the server and a single client, handling various types of messages
 * sent from the client and processing game logic related to the Go game.
 */
public class ServerConnection extends SocketConnection {
    private ClientHandler clientHandler;
    public GoGameServer goGameServer;

    /**
     * Initializes a new ServerConnection for a given client socket.
     *
     * @param socket The socket representing the client's connection.
     * @throws IOException If there is an error during socket connection setup.
     */
    /*@
        ensures clientHandler != null;
    */
    protected ServerConnection(Socket socket) throws IOException {
        super(socket);
    }

    /**
     * Sets the client handler for this server connection.
     *
     * @param clientHandler The client handler to associate with this connection.
     */
    /*@
        ensures clientHandler == \result;
    */
    public synchronized void setClientHandler(ClientHandler clientHandler) {
        this.clientHandler = clientHandler;
    }

    /**
     * Sends a message to the client associated with this connection.
     *
     * @param message The message to send to the client.
     */
    /*@
        ensures clientHandler.getSocket().isConnected();
    */
    public synchronized void sendServerMessage(String message) {
        super.sendMessage(message);
    }

    /**
     * Handles an error situation by sending an error message to the client and disconnecting the client.
     *
     * @param errorContent The content of the error message to send.
     */
    /*@
        ensures clientHandler.getConnected() == false;
    */
    private synchronized void handleErrorSituation(String errorContent) {
        sendServerMessage(ServerProtocol.ERROR + ServerProtocol.SEPARATOR.toString() + errorContent);
        clientHandler.handleDisconnect();
        clientHandler.close();
    }

    /**
     * Handles the incoming message from the client, processing it according to the message type.
     *
     * @param message The message received from the client.
     */
    /*@
        ensures clientHandler.getUsername() != null ==> clientHandler.getConnected();
    */
    @Override
    protected synchronized void handleMessage(String message) {
        System.out.println(clientHandler.hashCode() + ": " + message);

        String[] parts = message.split(ServerProtocol.SEPARATOR_ESCAPED.toString());
        if (parts.length == 0) return;

        if (!clientHandler.getConnected() &&
                !Objects.equals(parts[0], ServerProtocol.HELLO.toString())) {
            handleErrorSituation("Expected " + ServerProtocol.HELLO.toString() +
                                         " but did not receive it!");
            return;
        }

        if (clientHandler.getConnected() && clientHandler.getUsername() == null &&
                !parts[0].equals(ServerProtocol.LOGIN.toString())) {
            handleErrorSituation("Unexpected message opcode '" + parts[0] +
                                         "' full message: [" + String.join(", ", parts) + "]");
            return;
        }

        handleMessageType(parts);
    }

    /**
     * Handles the message type by dispatching to the appropriate handler.
     *
     * @param parts The split message parts to be handled.
     */
    /*@
        ensures (\exists String opcode; parts[0].equals(opcode));
    */
    private void handleMessageType(String[] parts) {
        switch (parts[0]) {
            case "HELLO":
                handleHello(parts);
                break;
            case "LOGIN":
                handleLogin(parts);
                break;
            case "LIST":
                handleList(parts);
                break;
            case "QUEUE":
                handleQueue(parts);
                break;
            case "MOVE":
                handleMove(parts);
                break;
            case "CHAT":
                handleChat(parts);
                break;
            case "WHISPER":
                handleWhisper(parts);
                break;
            case "RANK":
                handleRank(parts);
                break;
            case "CHALLENGE":
                handleChallenge(parts);
                break;
            case "ACCEPT":
                handleChallengeAccept(parts);
                break;
            case "REJECT":
                handleChallengeReject(parts);
                break;
            default:
                handleErrorSituation("Unexpected message opcode '" + parts[0] +
                                             "' full message: [" + String.join(", ", parts) + "]");
        }
    }

    /**
     * Handles the HELLO message from the client.
     *
     * @param parts The message parts.
     */
    /*@
        ensures clientHandler.getConnected() == true ==> clientHandler.getUsername() != null;
    */
    private void handleHello(String[] parts) {
        if (parts.length == 1) {
            handleErrorSituation("Received " + ServerProtocol.HELLO +
                                         " message without description!");
            return;
        }

        if (!clientHandler.getConnected()) {
            sendServerMessage(String.join(ServerProtocol.SEPARATOR.toString(), parts));
            clientHandler.setConnected(true);
            // Check for additional options
            for (String part : parts) {
                // CHAT
                if (part.equals(ServerProtocol.CHAT.toString())) {
                    clientHandler.setSupportsChat(true);
                } else if (part.equals(ServerProtocol.RANK.toString())) {
                    clientHandler.setSupportsRank(true);
                } else if (part.equals(ServerProtocol.NAMEDQUEUES.toString())) {
                    clientHandler.setSupportsNamedQueues(true);
                } else if (part.equals(ServerProtocol.CHALLENGE.toString())) {
                    clientHandler.setSupportsChallenge(true);
                }
            }
        } else {
            handleErrorSituation("Unexpected HELLO message after connection established");
        }
    }

    /**
     * Handles the LOGIN message and validates the username.
     *
     * @param parts The message parts.
     */
    /*@
        ensures !goGameServer.getPlayers().contains(clientHandler) ==> clientHandler.getUsername() != null;
    */
    private void handleLogin(String[] parts) {
        if (parts.length != 2) {
            handleErrorSituation("Received LOGIN message with invalid number of parameters!");
            return;
        }

        // Check if username already exists
        for (ClientHandler client : goGameServer.getPlayers()) {
            if (client != clientHandler &&
                    Objects.equals(client.getUsername(), parts[1])) {
                sendServerMessage(ServerProtocol.ALREADYLOGGEDIN.toString());
                return;
            }
        }

        clientHandler.receiveUsername(parts[1]);
        goGameServer.getPlayerWins().putIfAbsent(parts[1], 0);
        sendServerMessage(ServerProtocol.LOGIN.toString());
    }

    /**
     * Handles the LIST message to list all connected users.
     *
     * @param parts The message parts.
     */
    /*@
        ensures clientHandler.getUsername() != null ==> \result.contains(clientHandler.getUsername());
    */
    private void handleList(String[] parts) {
        if (parts.length != 1) {
            handleErrorSituation("Expected LIST message without parameters");
            return;
        }

        StringBuilder userList = new StringBuilder();
        for (ClientHandler client : goGameServer.getPlayers()) {
            if (client.getUsername() != null) {
                if (!userList.isEmpty()) {
                    userList.append(ServerProtocol.SEPARATOR);
                }
                userList.append(client.getUsername());
            }
        }

        sendServerMessage(ServerProtocol.LIST.toString() + ServerProtocol.SEPARATOR + userList);
    }

    /**
     * Handles the QUEUE message for players who wish to join a game.
     *
     * @param parts The message parts.
     */
    /*@
        ensures goGameServer.getQueuedPlayers().contains(clientHandler) == true;
    */
    private void handleQueue(String[] parts) {
        if (clientHandler.getSupportsNamedQueues() && parts.length > 2) {
            handleErrorSituation("Expected QUEUE with the names queue.");
            return;
        } else if (!clientHandler.getSupportsNamedQueues() && parts.length != 1) {
            handleErrorSituation("Received QUEUE with invalid parameters.");
            return;
        }

        if (parts.length == 1){
            Queue<ClientHandler> queue = goGameServer.getQueuedPlayers();
            if (clientHandler.getOpponent() == null) {
                if (queue.contains(clientHandler)) {
                    queue.remove(clientHandler);
                } else {
                    queue.add(clientHandler);
                }
            }

            if (queue.size() >= 2) {
                startNewGame(queue);
            }
            return;
        }

        Queue<ClientHandler> namedQueue = goGameServer.getNamedQueue(parts[1]);
        if (clientHandler.getOpponent() == null) {
            if (namedQueue.contains(clientHandler)){
                namedQueue.remove(clientHandler);
            } else {
                namedQueue.add(clientHandler);
            }
        }

        if (namedQueue.size() >= 2) {
            startNewGame(namedQueue);
        }
    }

    /**
     * Starts a new game between two players from the queue.
     *
     * @param queue The queue of players waiting for a game.
     */
    /*@
        ensures clientHandler.getCurrentGame() != null;
    */
    private void startNewGame(Queue<ClientHandler> queue) {
        ClientHandler player1 = queue.poll();
        ClientHandler player2 = queue.poll();

        if (player1 == null || player2 == null) return;

        // Set opponents
        player1.setOpponent(player2);
        player2.setOpponent(player1);

        // Create player representations
        AbstractPlayer player1Rep = new HumanPlayer(player1.getUsername(), Stone.BLACK);
        AbstractPlayer player2Rep = new HumanPlayer(player2.getUsername(), Stone.WHITE);

        // Create game
        Game game = new GoGame(7, player1Rep, player2Rep);

        // Set game and players
        player1.setCurrentGame(game);
        player2.setCurrentGame(game);
        player1.setThisPlayer(player1Rep);
        player2.setThisPlayer(player2Rep);

        // Announce game start
        String gameStartMessage = ServerProtocol.NEWGAME.toString() + ServerProtocol.SEPARATOR +
                player1.getUsername() + ServerProtocol.SEPARATOR +
                player2.getUsername();

        player1.sendServerMessage(player1.getUsername(), gameStartMessage);
        player2.sendServerMessage(player2.getUsername(), gameStartMessage);
    }

    /**
     * Handles the MOVE message for a player making a move.
     *
     * @param parts The message parts.
     */
    /*@
        ensures clientHandler.getCurrentGame().isValidMove(\result);
    */
    private void handleMove(String[] parts) {
        if (parts.length != 2) {
            handleErrorSituation("MOVE requires exactly one argument.");
            return;
        }

        Game currentGame = clientHandler.getCurrentGame();
        if (currentGame == null) {
            handleErrorSituation("Cannot make a move - no active game");
            return;
        }

        ClientHandler opponent = clientHandler.getOpponent();
        if (opponent == null) {
            handleErrorSituation("Cannot make a move - no opponent");
            return;
        }

        try {
            int move = Integer.parseInt(parts[1]);
            Stone stone = clientHandler.getThisPlayer().getPlayerStone();
            Move potentialMove = new GoMove(move / 7, move % 7, stone);

            if (currentGame.isValidMove(potentialMove)) {
                currentGame.doMove(potentialMove);

                // Broadcast move to both players
                String moveMessage = ServerProtocol.MOVE.toString() + ServerProtocol.SEPARATOR + parts[1];
                clientHandler.sendServerMessage(clientHandler.getUsername(), moveMessage);
                opponent.sendServerMessage(opponent.getUsername(), moveMessage);

                // Check for winner
                Player winner = currentGame.getWinner();
                if (winner != null) {
                    goGameServer.incrementWins(currentGame.getWinner().getName());
                    String winMessage = ServerProtocol.GAMEOVER.toString() + ServerProtocol.SEPARATOR +
                            ServerProtocol.VICTORY + ServerProtocol.SEPARATOR + winner.getName();
                    clientHandler.sendServerMessage(clientHandler.getUsername(), winMessage);
                    opponent.sendServerMessage(opponent.getUsername(), winMessage);

                    // Clean up game state
                    cleanupGame(clientHandler, opponent);
                }
            } else {
                handleErrorSituation("Invalid move position: " + move);
            }
        } catch (NumberFormatException e) {
            handleErrorSituation("Invalid move format");
        }
    }

    private void handleChat(String[] parts) {
        if (parts.length != 2) {
            handleErrorSituation("CHAT requires exactly one argument.");
            return;
        }

        // Send the message to all that have the CHAT extension
        for (ClientHandler client : goGameServer.getPlayers()) {
            if (!client.equals(this.clientHandler) && client.getSupportsChat()) {
                client.sendServerMessage(this.clientHandler.getUsername(),
                                         ServerProtocol.CHAT.toString() +
                                                 ServerProtocol.SEPARATOR +
                                                 this.clientHandler.getUsername() +
                                                 ServerProtocol.SEPARATOR +
                                                 parts[1]);
            }
        }
    }

    private void handleWhisper(String[] parts) {
        if (parts.length != 3) {
            handleErrorSituation("CHAT requires exactly one argument.");
            return;
        }

        // Send the message to all that have the CHAT extension
        for (ClientHandler client : goGameServer.getPlayers()) {
            if (client.getUsername().equals(parts[1]) && client.getSupportsChat()) {
                client.sendServerMessage(this.clientHandler.getUsername(),
                                         ServerProtocol.WHISPER.toString() +
                                                 ServerProtocol.SEPARATOR +
                                                 this.clientHandler.getUsername() +
                                                 ServerProtocol.SEPARATOR +
                                                 parts[2]);
                return;
            }
        }
        this.clientHandler.sendServerMessage(this.clientHandler.getUsername(), ServerProtocol.CANNOTWHISPER.toString() +
                ServerProtocol.SEPARATOR + parts[1]);
    }

    private void handleRank(String[] parts) {
        if (!this.clientHandler.getSupportsRank()) {
            handleErrorSituation("Unknown opcode RANK");
            return;
        }

        if (parts.length != 1) {
            handleErrorSituation("Received RANK but with invalid parameters!");
            return;
        }

        if (goGameServer.getPlayerWins().isEmpty()) {
            String message = "";
            for (ClientHandler client : goGameServer.getPlayers()) {
                message += ServerProtocol.SEPARATOR + client.getUsername() + ServerProtocol.SEPARATOR + "0";
            }
            this.clientHandler.sendServerMessage(this.clientHandler.getUsername(), ServerProtocol.RANK + message);
            return;
        }

        Map<String, Integer> sortedDescMap = goGameServer.getPlayerWins().entrySet().stream()
                .sorted(Map.Entry.<String, Integer>comparingByValue().reversed())
                .collect(Collectors.toMap(
                        Map.Entry::getKey,
                        Map.Entry::getValue,
                        (e1, e2) -> e1,
                        LinkedHashMap::new
                ));

        String message = "";
        for (String player : sortedDescMap.keySet()) {
            message += ServerProtocol.SEPARATOR + player + ServerProtocol.SEPARATOR + sortedDescMap.get(player);
        }
        this.clientHandler.sendServerMessage(this.clientHandler.getUsername(), ServerProtocol.RANK + message);
    }

    private void handleChallenge(String[] parts) {
        if (!this.clientHandler.getSupportsChallenge()) {
            handleErrorSituation("Unexpected Opcode CHALLENGE, unsupported extension");
            return;
        }

        if (parts.length != 2) {
            handleErrorSituation("CHALLENGE requires exactly one argument.");
            return;
        }

        if (this.clientHandler.getOpponent() != null) {
            handleErrorSituation("Cannot challenge while in a game.");
            return;
        }

        for (ClientHandler cl : goGameServer.getQueuedPlayers()) {
            if (clientHandler.equals(cl)) {
                clientHandler.handleDisconnect();
                handleErrorSituation("Cannot challenge while in queue.");
                return;
            }
        }

        for (String nq : goGameServer.getNamedQueues().keySet()) {
            for (ClientHandler cl : goGameServer.getNamedQueue(nq)) {
                if (clientHandler.equals(cl)) {
                    clientHandler.handleDisconnect();
                    handleErrorSituation("Cannot challenge while in queue.");
                    return;
                }
            }
        }

        // Check if the client disconnected
        if (!goGameServer.getPlayers().contains(this.clientHandler)) {
            // The challenger disconnected
            return;
        }

        for (ClientHandler player : goGameServer.getPlayers()) {
            if (player.getUsername().equals(parts[1]) && !player.equals(this.clientHandler)) {
                // Checks for invalidity
                if (player.getOpponent() != null || !player.getSupportsChallenge()) {
                    this.clientHandler.sendServerMessage(player.getUsername(), ServerProtocol.REJECT.toString() +
                            ServerProtocol.SEPARATOR +
                            player.getUsername());
                    return;
                }

                // In case we can send the challenge
                player.sendServerMessage(player.getUsername(), ServerProtocol.CHALLENGE.toString() +
                        ServerProtocol.SEPARATOR +
                        this.clientHandler.getUsername());
                return;
            }
        }

        this.clientHandler.sendServerMessage(parts[1], ServerProtocol.REJECT.toString() +
                ServerProtocol.SEPARATOR +
                parts[1]);
        return;
    }

    private void handleChallengeAccept(String[] parts) {
        if (parts.length != 2) {
            handleErrorSituation("ACCEPT requires exactly one argument.");
            return;
        }

        for (ClientHandler player : goGameServer.getPlayers()) {
            if (player.getUsername().equals(parts[1])) {
                if (player.getOpponent() != null) {
                    return;
                }
                Queue<ClientHandler> q = new LinkedList<>();
                q.add(player);
                q.add(this.clientHandler);
                startNewGame(q);
                return;
            }
        }
    }

    private void handleChallengeReject(String[] parts) {
        if (parts.length != 2) {
            handleErrorSituation("ACCEPT requires exactly one argument.");
            return;
        }

        for (ClientHandler player : goGameServer.getPlayers()) {
            if (player.getUsername().equals(parts[1])) {
                if (player.getOpponent() != null) {
                    return;
                }
                player.sendServerMessage(player.getUsername(), ServerProtocol.REJECT.toString() +
                        ServerProtocol.SEPARATOR +
                        this.clientHandler.getUsername());
            }
        }
    }

    /**
     * Cleans up the game state by disconnecting the players from the game.
     *
     * @param player1 The first player.
     * @param player2 The second player.
     */
    /*@
        ensures player1.getCurrentGame() == null && player2.getCurrentGame() == null;
    */
    void cleanupGame(ClientHandler player1, ClientHandler player2) {
        player1.setCurrentGame(null);
        player1.setThisPlayer(null);
        player1.setOpponent(null);
        player2.setCurrentGame(null);
        player2.setThisPlayer(null);
        player2.setOpponent(null);
    }

    /**
     * Handles the disconnection of the client from the server.
     */
    /*@
        ensures clientHandler.getConnected() == false;
    */
    @Override
    protected synchronized void handleDisconnect() {
        clientHandler.handleDisconnect();
    }
}