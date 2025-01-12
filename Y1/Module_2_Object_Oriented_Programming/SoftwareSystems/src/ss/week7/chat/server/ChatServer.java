package ss.week7.chat.server;

import java.io.IOException;
import java.net.Socket;
import java.util.HashSet;
import java.util.Scanner;
import java.util.concurrent.locks.ReentrantLock;
import ss.networking.SocketServer;

// 7.3 Answer - you create a strategy for the UI and you have it in the code as an interface which
// Allows us to easily swap the Interfaces

public class ChatServer extends SocketServer {
    private final HashSet<ClientHandler> clientHandlers;
    private final ReentrantLock lock = new ReentrantLock();

    public ChatServer(int port) throws IOException {
        super(port);
        clientHandlers = new HashSet<>();
    }

    @Override
    public void acceptConnections() throws IOException {
        super.acceptConnections();
    }

    @Override
    protected void handleConnection(Socket socket) {
        try {
            ServerConnection serverConnection = new ServerConnection(socket);
            ClientHandler clientHandler = new ClientHandler(socket);

            serverConnection.setClientHandler(clientHandler);
            serverConnection.chatServer = this;

            clientHandler.setServerConnection(serverConnection);
            clientHandler.chatServer = this;

            addClient(clientHandler);
            serverConnection.start();
        } catch (IOException e) {
            throw new RuntimeException("Error handling client connection.", e);
        }
    }

    public void addClient(ClientHandler clientHandler) {
        lock.lock();
        try {
            clientHandlers.add(clientHandler);
            System.out.println("Client added: " + clientHandler.hashCode());
        } finally {
            lock.unlock();
        }
    }

    public void removeClient(ClientHandler clientHandler) {
        lock.lock();
        try {
            clientHandlers.remove(clientHandler);
            System.out.println("Client removed: " + clientHandler.hashCode());
        } finally {
            lock.unlock();
        }
    }

    public void handleChatMessage(ClientHandler clientHandler, String message) {
        //clientHandler.sendChatMessage(clientHandler.getUsername(), message);
        for (ClientHandler cl : clientHandlers) {
            if (cl.getUsername() != null) {
                cl.sendChatMessage(clientHandler.getUsername(), message);
            }
        }
    }

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

        ChatServer chat = new ChatServer(port_num);
        System.out.println("Server started on port " + chat.getPort());
        chat.acceptConnections();
    }
}
