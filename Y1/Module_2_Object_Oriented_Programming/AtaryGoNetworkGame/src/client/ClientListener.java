package client;

public interface ClientListener {
    /**
     * Called when the connection to the server is lost.
     */
    void connectionLost();
}
