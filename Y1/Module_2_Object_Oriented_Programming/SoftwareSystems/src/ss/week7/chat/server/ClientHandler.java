package ss.week7.chat.server;

import java.io.IOException;
import java.net.Socket;
import ss.networking.SocketConnection;

public class ClientHandler extends SocketConnection {

    public ServerConnection serverConnection;
    public ChatServer chatServer;
    private String username = null;

    /**
     * Constructs a new client handler for the given socket.
     *
     * @param socket the socket for the connection
     * @throws IOException if an error occurs initializing the connection
     */
    public ClientHandler(Socket socket) throws IOException {
        super(socket);
    }

    public void setServerConnection(ServerConnection serverConnection) {
        this.serverConnection = serverConnection;
    }

    /**
     * Handles incoming messages from the server.
     *
     * @param message the message received
     */
    @Override
    public synchronized void handleMessage(String message) {
        if (username != null) {
            System.out.println(username + ": " + message);
            //System.out.println(message);
            chatServer.handleChatMessage(this, message);
        }
    }

    public void sendChatMessage(String username, String message) {
        serverConnection.sendChatMessage(username, message);
    }

    /**
     * Handles client disconnection.
     */
    @Override
    public synchronized void handleDisconnect() {
        if (username != null) {
            System.out.println(username + " has left the chat.");
        }
        chatServer.removeClient(this);
    }

    /**
     * Receives and sets the username for this client.
     *
     * @param username the username to set
     */
    public synchronized void receiveUsername(String username) {
        if (this.username == null) {
            this.username = username;
            System.out.println("Username set to: " + username);
        }
    }

    public void receiveChatMessage(String message) {
        // TODO: need to send the data via an Output Writer
    }

    public String getUsername() {
        return username;
    }
}
