package ss.week7.chat.client;

import java.io.IOException;
import java.net.InetAddress;
import ss.networking.SocketConnection;
import ss.week7.chat.protocol.Protocol;

public class ClientConnection extends SocketConnection {
    private ChatClient chatClient;

    protected ClientConnection(InetAddress address, int port) throws IOException {
        super(address, port);
    }

    @Override
    protected void handleMessage(String message) {
        if (message == null || message.isEmpty()) {
            return;
        }

        String[] components = message.split(Protocol.SEPARATOR);

        // Verify message format matches protocol
        if (components.length >= 3 && components[0].equals(Protocol.FROM)) {
            chatClient.receiveChatMessage(components[1], components[2]);
        }
    }

    @Override
    protected void handleDisconnect() {
        if (chatClient != null) {
            chatClient.handleDisconnect();
        }
    }

    public void setChatClient(ChatClient chatClient) {
        this.chatClient = chatClient;
    }

    public void sendUsername(String username) {
        sendMessage(Protocol.USER + Protocol.SEPARATOR + username);
    }

    public void sendChatMessage(String message) {
        sendMessage(Protocol.SAY + Protocol.SEPARATOR + message);
    }
}
