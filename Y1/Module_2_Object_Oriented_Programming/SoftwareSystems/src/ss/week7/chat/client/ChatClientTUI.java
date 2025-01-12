package ss.week7.chat.client;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;
import ss.week7.chat.protocol.Protocol;

/**
 * Text-based user interface for the chat client.
 */
public class ChatClientTUI implements ClientListener {
    private ChatClient chatClient;

    @Override
    public void chatMessage(String username, String message) {
        // Print messages immediately when received
        System.out.println(username + ": " + message);
    }

    @Override
    public void connectionLost() {
        System.out.println("Connection to server lost!");
        System.exit(1);
    }

    public void runTUI() {
        Scanner scanner = new Scanner(System.in);

        try {
            // Get server details
            System.out.print("Enter the server address: ");
            String host = scanner.nextLine();
            System.out.print("Enter the server port: ");
            int port = Integer.parseInt(scanner.nextLine());

            // Initialize client and start connection
            chatClient = new ChatClient(InetAddress.getByName(host), port);
            chatClient.getConnection().start();

            // Register as listener
            chatClient.addListener(this);

            // Get username and send to server
            System.out.print("Enter your username: ");
            String username = scanner.nextLine();
            chatClient.sendUsername(username);

            // Main message loop
            System.out.println("You can now start chatting (type 'quit' to exit)");
            while (true) {
                String message = scanner.nextLine();
                if (message.equalsIgnoreCase("quit")) {
                    break;
                }
                chatClient.sendChatMessage(message);
            }

        } catch (UnknownHostException e) {
            System.err.println("Error: Invalid server address");
        } catch (NumberFormatException e) {
            System.err.println("Error: Invalid port number");
        } finally {
            if (chatClient != null) {
                chatClient.removeListener(this);
                chatClient.close();
            }
        }
    }

    public static void main(String[] args) {
        new ChatClientTUI().runTUI();
    }
}