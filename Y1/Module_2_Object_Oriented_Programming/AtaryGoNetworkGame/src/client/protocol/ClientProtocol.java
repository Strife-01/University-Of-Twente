package client.protocol;

/**
 * Represents the different protocol commands used in the client-server communication.
 * Each command corresponds to a specific action or request within the protocol.
 * <p>
 * The protocol commands are used to interact with the server, including login, game moves,
 * and error handling.
 * </p>
 */
public enum ClientProtocol {

    /**
     * Command for initiating a hello message with optional client description and extensions.
     */
    HELLO("HELLO"),

    /**
     * Command for logging in with a username.
     */
    LOGIN("LOGIN"),

    /**
     * Response from the server indicating that the user is already logged in.
     */
    ALREADYLOGGEDIN("ALREADYLOGGEDIN"),

    /**
     * Command for requesting the list from the server.
     */
    LIST("LIST"),

    /**
     * Command to indicate that the client wants to take part in the server.
     */
    QUEUE("QUEUE"),

    /**
     * Command to send a move in the game, where N is a number between 0 and 48 (inclusive).
     */
    MOVE("MOVE"),

    /**
     * Command for signaling an error, optionally with an error description.
     */
    ERROR("ERROR"),

    /**
     * Separator used to delimit parts of the protocol message.
     */
    SEPARATOR("~"),

    /**
     * Command to start a new game.
     */
    NEWGAME("NEWGAME"),

    /**
     * Command to quit the client.
     */
    QUIT_CLIENT("QUIT_CLIENT"),

    /**
     * Separator escaped for when we have ~ in the message.
     */
    SEPARATOR_ESCAPED("(?<!\\\\)~"),

    /**
     * Handles the embedded chat.
     */
    CHAT("CHAT"),

    /**
     * Handles targeted messages.
     */
    WHISPER("WHISPER"),

    /**
     * Informs sender that the target cannot receive message.
     */
    CANNOTWHISPER("CANNOTWHISPER"),

    /**
     * The rank of the players on the server.
     */
    RANK("RANK"),

    /**
     * The client supports named queues.
     */
    NAMEDQUEUES("NAMEDQUEUES"),

    /**
     * The client supports player challenging another.
     */
    CHALLENGE("CHALLENGE"),

    /**
     * Indicates the client rejected the challenge.
     */
    REJECT("REJECT"),

    /**
     * Indicates the client accepted the challenge.
     */
    ACCEPT("ACCEPT");



    private final String protocol_command;

    /**
     * Constructs a protocol command with the specified string representation.
     *
     * @param protocol_command the string representation of the protocol command
     */
    ClientProtocol(String protocol_command) {
        this.protocol_command = protocol_command;
    }

    /**
     * Returns the string representation of the protocol command.
     *
     * @return the string value of the protocol command
     */
    @Override
    public String toString() {
        return String.valueOf(this.protocol_command);
    }
}
