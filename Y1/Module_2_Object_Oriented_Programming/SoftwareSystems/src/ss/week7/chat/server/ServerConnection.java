package ss.week7.chat.server;

import java.io.IOException;
import java.net.Socket;
import ss.networking.SocketConnection;
import ss.week7.chat.protocol.Protocol;

public class ServerConnection extends SocketConnection {
    private ClientHandler clientHandler;
    public ChatServer chatServer;

    /**
     * Constructs a new server connection for the given socket.
     *
     * @param socket the socket for this connection
     * @throws IOException if an error occurs initializing the connection
     */
    protected ServerConnection(Socket socket) throws IOException {
        super(socket);
    }

    /**
     * Associates a client handler with this server connection.
     *
     * @param clientHandler the client handler to associate
     */
    public synchronized void setClientHandler(ClientHandler clientHandler) {
        this.clientHandler = clientHandler;
    }

    public synchronized void sendChatMessage(String username, String message) {
        super.sendMessage(Protocol.FROM + Protocol.SEPARATOR + username + Protocol.SEPARATOR + message);
    }

    /**
     * Handles messages received from clients.
     *
     * @param message the message received
     */
    @Override
    protected synchronized void handleMessage(String message) {
        String[] parts = message.split(Protocol.SEPARATOR);

        if (message.startsWith(Protocol.USER) && parts.length >= 2) {
            clientHandler.receiveUsername(parts[1].trim());
        } else if (message.startsWith(Protocol.SAY) && parts.length >= 2) {
            clientHandler.handleMessage(parts[1].trim());
        }
    }

    /**
     * Handles client disconnection.
     */
    @Override
    protected synchronized void handleDisconnect() {
        clientHandler.handleDisconnect();
    }
}
