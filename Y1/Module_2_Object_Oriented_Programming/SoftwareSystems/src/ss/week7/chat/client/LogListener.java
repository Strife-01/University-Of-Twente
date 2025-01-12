package ss.week7.chat.client;

import java.io.FileWriter;
import java.io.IOException;

public class LogListener implements ClientListener {
    private FileWriter fileWriter;
    private String hashNameRepresentation;

    public LogListener(String listenerObject) throws IOException {
        fileWriter = new FileWriter("src/ss/week7/chat/client/" + listenerObject + "chat_logs.txt", true);
        hashNameRepresentation = listenerObject;
    }

    /**
     * @return the hash name representation of the log listener
     */
    public String getHashNameRepresentation() {
        return hashNameRepresentation;
    }

    /**
     * Called when a chat message is received.
     *
     * @param username The sender's username
     * @param message  The message content
     */
    @Override
    public void chatMessage(String username, String message) {
        try {
            fileWriter.write("<" + username + ">" + " said: " + "\"<" + message + ">\"\n");
            fileWriter.flush();
        } catch (IOException e) {
            System.out.println("We could not write to the log file...");
        }
    }

    /**
     * Called when the connection to the server is lost.
     */
    @Override
    public void connectionLost() {
        try {
            fileWriter.flush();
            fileWriter.close();
            System.out.println("The log file has been successfully closed...");
        } catch (IOException e) {
            System.out.println("The log file could not be closed...");
        }
    }
}
