package server;

import java.io.IOException;
import java.net.Socket;
import java.util.*;
import java.util.concurrent.locks.ReentrantLock;
import network_abstractions.SocketServer;

/**
 * This class represents the GoGameServer, a server for handling multiplayer Go game sessions.
 * It accepts client connections, manages queued players, and handles chat messages between clients.
 */
public class GoGameServer extends SocketServer {
    private final HashSet<ClientHandler> clientHandlers;
    private final ReentrantLock lock = new ReentrantLock();
    private final Queue<ClientHandler> queuedPlayers;
    private final HashMap<String, Queue<ClientHandler>> namedQueues;
    private final HashMap<String, Integer> playerWins;

    /**
     * Creates a new GoGameServer instance bound to the specified port.
     *
     * @param port The port number to bind the server to.
     * @throws IOException If there is an error during server initialization.
     */
    /*@
        ensures clientHandlers != null;
        ensures queuedPlayers != null;
    */
    public GoGameServer(int port) throws IOException {
        super(port);
        clientHandlers = new HashSet<>();
        queuedPlayers = new LinkedList<>();
        namedQueues = new HashMap<>();
        playerWins = new HashMap<>();
    }

    public synchronized int getWins(String username) {
        Integer wins = playerWins.get(username);
        if (wins == null) {
            return 0;
        }
        return wins;
    }

    public synchronized void incrementWins(String username) {
        Integer wins = playerWins.get(username);
        if (wins == null) {
            playerWins.put(username, 1);
        } else {
            playerWins.put(username, ++wins);
        }
    }

    public synchronized HashMap<String, Integer> getPlayerWins() {
        return this.playerWins;
    }

    public synchronized HashMap<String, Queue<ClientHandler>> getNamedQueues() {
        return this.namedQueues;
    }

    /**
     * Accepts incoming client connections.
     *
     * @throws IOException If there is an error while accepting connections.
     */
    /*@
        ensures (\forall ClientHandler ch; clientHandlers.contains(ch) ==> ch.getConnected());
    */
    @Override
    public void acceptConnections() throws IOException {
        super.acceptConnections();
    }

    /**
     * Handles the connection of a new client.
     *
     * @param socket The socket connection of the client.
     */
    /*@
        ensures serverConnection != null;
        ensures clientHandler != null;
    */
    @Override
    protected void handleConnection(Socket socket) {
        try {
            ServerConnection serverConnection = new ServerConnection(socket);
            ClientHandler clientHandler = new ClientHandler(socket);

            serverConnection.setClientHandler(clientHandler);
            serverConnection.goGameServer = this;

            clientHandler.setServerConnection(serverConnection);
            clientHandler.setGoGameServer(this);

            addClient(clientHandler);
            serverConnection.start();
        } catch (IOException e) {
            throw new RuntimeException("Error handling client connection.", e);
        }
    }

    /**
     * Adds a client handler to the server's list of clients.
     *
     * @param clientHandler The client handler to add.
     */
    /*@
        ensures clientHandlers.contains(clientHandler);
    */
    public void addClient(ClientHandler clientHandler) {
        lock.lock();
        try {
            clientHandlers.add(clientHandler);
            System.out.println("Client added: " + clientHandler.hashCode());
        } catch (Exception e) {
            System.out.println("Client could not be added");
        } finally {
            lock.unlock();
        }
    }

    /**
     * Removes a client handler from the server's list of clients.
     *
     * @param clientHandler The client handler to remove.
     */
    /*@
        ensures !clientHandlers.contains(clientHandler);
    */
    public void removeClient(ClientHandler clientHandler) {
        lock.lock();
        try {
            clientHandlers.remove(clientHandler);
            System.out.println("Client removed: " + clientHandler.hashCode());
        } catch (Exception e) {
            System.out.println("Client could not be added");
        } finally {
            lock.unlock();
        }
    }

    /**
     * Handles a chat message from a client by sending it to all connected clients.
     *
     * @param clientHandler The client who sent the message.
     * @param message The message to broadcast to all clients.
     */
    /*@
        ensures (\forall ClientHandler cl; cl.getUsername() != null ==> cl.getUsername().equals(clientHandler.getUsername()));
    */
    public void handleChatMessage(ClientHandler clientHandler, String message) {
        for (ClientHandler cl : clientHandlers) {
            if (cl.getUsername() != null) {
                cl.sendServerMessage(clientHandler.getUsername(), message);
            }
        }
    }

    /**
     * Retrieves the set of all connected players.
     *
     * @return The set of connected players.
     */
    /*@
        ensures \result == clientHandlers;
    */
    public synchronized HashSet<ClientHandler> getPlayers() {
        return this.clientHandlers;
    }

    /**
     * Retrieves the queue of players waiting to join a game.
     *
     * @return The queue of queued players.
     */
    /*@
        ensures \result == queuedPlayers;
    */
    public synchronized Queue<ClientHandler> getQueuedPlayers() {
        return this.queuedPlayers;
    }

    public synchronized Queue<ClientHandler> getNamedQueue(String queueName) {
        Queue<ClientHandler> namedQueue = this.namedQueues.get(queueName);
        if (namedQueue == null) {
            this.namedQueues.put(queueName, new LinkedList<ClientHandler>());
        }
        namedQueue = this.namedQueues.get(queueName);
        return namedQueue;
    }

    /**
     * Starts the GoGameServer, prompting the user for a valid port number and accepting incoming connections.
     *
     * @param args Command-line arguments (not used).
     * @throws IOException If there is an error during server startup or connection handling.
     */
    /*@
        ensures gameServer.getPort() == port_num;
    */
    public static void main(String[] args) throws IOException {
        Scanner sc = new Scanner(System.in);
        System.out.print("Please enter a port number: ");
        String port = sc.nextLine();
        int port_num;

        while (!port.matches("\\d+") || (port_num = Integer.parseInt(port)) < 0 ||
                (port_num = Integer.parseInt(port)) > 65355) {
            System.out.print("Invalid input. Enter a valid port (0-65535): ");
            port = sc.nextLine();
        }

        GoGameServer gameServer = new GoGameServer(port_num);
        System.out.println("Server started on port " + gameServer.getPort());
        gameServer.acceptConnections();
    }
}
