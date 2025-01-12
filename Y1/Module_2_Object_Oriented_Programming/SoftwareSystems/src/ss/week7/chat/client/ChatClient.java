package ss.week7.chat.client;

import java.io.IOException;
import java.net.InetAddress;
import java.util.HashSet;
import java.util.Set;

public class ChatClient {
    private final ClientConnection connection;
    private final Set<ClientListener> listeners;
    private final Set<LogListener> logListeners;

    public ChatClient(InetAddress address, int port) {
        try {
            connection = new ClientConnection(address, port);
            connection.setChatClient(this);
            listeners = new HashSet<>();
            logListeners = new HashSet<>();
        } catch (IOException e) {
            throw new RuntimeException("Failed to create client connection: " + e.getMessage());
        }
    }

    public ClientConnection getConnection() {
        return connection;
    }

    public void close() {
        connection.close();
    }

    public synchronized void receiveChatMessage(String username, String message) {
        for (ClientListener listener : listeners) {
            listener.chatMessage(username, message);
        }
        for (LogListener logListener : logListeners) {
            logListener.chatMessage(username, message);
        }
    }

    public synchronized void handleDisconnect() {
        for (ClientListener listener : listeners) {
            listener.connectionLost();
        }
        for (LogListener logListener : logListeners) {
            logListener.connectionLost();
        }
    }

    public void sendUsername(String username) {
        connection.sendUsername(username);
    }

    public void sendChatMessage(String message) {
        connection.sendChatMessage(message);
    }

    public synchronized void addListener(ClientListener listener) {
        listeners.add(listener);
        try {
            logListeners.add(new LogListener(String.valueOf(listener.hashCode())));
        } catch (IOException e) {
            System.out.println("Could not create logListener...");
        }
    }

    public synchronized void removeListener(ClientListener listener) {
        listeners.remove(listener);
        for (LogListener logListener : logListeners) {
            if (logListener.getHashNameRepresentation()
                    .equals(String.valueOf(listener.hashCode()))) {
                logListeners.remove(logListener);
                logListener.connectionLost();
                break;
            }
        }
    }
}