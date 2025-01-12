package ss.week7.chat.client;

public interface ClientListener {
    /**
     * Called when a chat message is received.
     * @param username The sender's username
     * @param message The message content
     */
    void chatMessage(String username, String message);

    /**
     * Called when the connection to the server is lost.
     */
    void connectionLost();
}
