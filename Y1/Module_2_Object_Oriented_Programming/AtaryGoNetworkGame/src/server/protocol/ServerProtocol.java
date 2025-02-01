package server.protocol;

/**
 * Represents the different protocol commands used in the server-client communication.
 * Each command corresponds to a specific action or request within the server-side protocol.
 * <p>
 * The protocol commands are used to interact with the client, including login, game moves,
 * game over states, and error handling.
 * </p>
 */
public enum ServerProtocol {

    /**
     * Command for the server to send a hello message with optional description and extensions.
     */
    HELLO("HELLO"),

    /**
     * Command for the server to log in with a given username.
     */
    LOGIN("LOGIN"),

    /**
     * Response from the server indicating that the username or extension is already logged in.
     */
    ALREADYLOGGEDIN("ALREADYLOGGEDIN"),

    /**
     * Command for the server to send a list, optionally filtered by username.
     */
    LIST("LIST"),

    /**
     * Command to start a new game, specifying player 1 and player 2 names.
     */
    NEWGAME("NEWGAME"),

    /**
     * Command for the server to send a move made by a player in the game.
     */
    MOVE("MOVE"),

    /**
     * Command to indicate the end of the game with a reason and an optional winner.
     */
    GAMEOVER("GAMEOVER"),

    /**
     * Command for the server to disconnect, usually with a reason.
     */
    DISCONNECT("DISCONNECT"),

    /**
     * Command to indicate that a player has won, usually with a reason.
     */
    VICTORY("VICTORY"),

    /**
     * Command to indicate a draw, usually with a reason.
     */
    DRAW("DRAW"),

    /**
     * Command for signaling an error, optionally with a description.
     */
    ERROR("ERROR"),

    /**
     * Command to put the client in the server queue.
     */
    QUEUE("QUEUE"),

    /**
     * Separator used to delimit parts of the protocol message.
     */
    SEPARATOR("~"),

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
    ServerProtocol(String protocol_command) {
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
