package client;

import client.ClientListener;
import client.protocol.ClientProtocol;
import game.implementations.Board;
import game.utils.Stone;
import java.io.IOException;
import java.net.InetAddress;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Scanner;
import java.util.concurrent.locks.Lock;
import server.protocol.ServerProtocol;

import static game.utils.ConsoleColors.*;

/**
 * A text-based user interface for interacting with a Go game client.
 * This class provides functionality to connect to a server, perform a handshake,
 * join a game, play a turn either as a human or AI, and display the game state.
 * It handles communication with the server and manages player actions during the game.
 */
public class GoGameClientTUI implements ClientListener {
    private GoGameClient gameClient;
    private Scanner scanner;

    /*@ private invariant gameClient != null;
      @ private invariant scanner != null;
    */

    // Player Type FLAGS
    private final short IDLE_STATE = -1;
    private final short humanPlayer = 0;
    private final short naiveAI = 1;
    private final short mediumAI = 2;

    private short currentPlayerType = IDLE_STATE;
    private String namedQueue = null;
    private boolean isNamedQueue = false;

    // UX FLAGS
    private boolean activateHint = false;
    private boolean sendMessage = false;

    /**
     * Initializes the GoGameClientTUI object.
     * Initializes the scanner for user input.
     *
     * @throws NullPointerException if scanner is null
     */
    /*@ requires scanner == null;
      @ assignable scanner;
      @ ensures scanner != null;
    */
    public GoGameClientTUI() {
        scanner = new Scanner(System.in);
    }

    /**
     * Callback method when the connection to the server is lost.
     * Terminates the program upon a connection loss.
     */
    /*@ assignable \nothing;
    */
    @Override
    public void connectionLost() {
        System.out.println("Connection to server lost!");
        System.exit(1);
    }

    /**
     * Initializes the game client by establishing the connection, performing the handshake,
     * and setting the username.
     *
     */
    /*@ requires gameClient == null;
      @ requires gameClient != null;
      @ ensures gameClient != null;
      @ assignable gameClient;
      @ ensures gameClient != null;
      @*/
    private void handshakeInitialization() {
        establishConnection();
        performHandshake();
        setUsername();
        gameClient.addListener(this);
    }

    /**
     * Establishes the connection to the game server.
     * Continuously attempts to connect if an IOException occurs.
     *
     */
    /*@ requires gameClient == null;
      @ ensures gameClient != null;
      @ assignable gameClient;
    */
    private void establishConnection() {
        while (true) {
            try {
                String host = promptForHost();
                int port = promptForPort(host);
                gameClient = new GoGameClient(InetAddress.getByName(host), port);
                gameClient.setSetUp(true);
                gameClient.getConnection().start();
                return;
            } catch (IOException e) {
                System.out.println("Could not connect to server. Please try again.");
            }
        }
    }

    /**
     * Prompts the user for the server host address.
     *
     * @return The entered host address as a String.
     *
     * @throws NullPointerException if user input is null
     */
    /*@ requires scanner != null;
      @ ensures \result != null;
      @ assignable scanner;
    */
    private String promptForHost() {
        System.out.print("Enter server address: ");
        return scanner.nextLine();
    }

    /**
     * Prompts the user for the server port based on the host address.
     *
     * @param host The host address to associate with the port.
     * @return The entered port number as an integer.
     *
     * @throws IllegalArgumentException if port is not between 0 and 65535
     */
    /*@ requires host != null;
      @ ensures (\result >= 0 && \result <= 65535);
      @ assignable scanner;
    */
    private int promptForPort(String host) {
        while (true) {
            System.out.print("Enter server port for " + host + ": ");
            try {
                int port = Integer.parseInt(scanner.nextLine());
                if (port >= 0 && port <= 65535) {
                    return port;
                }
                System.out.println("Port must be between 0 and 65535");
            } catch (NumberFormatException e) {
                System.out.println("Invalid port number");
            }
        }
    }

    /**
     * Performs a handshake with the server to establish the connection.
     * Sends the initial hello message and waits for the server response.
     *
     */
    /*@ requires gameClient != null;
      @ ensures gameClient.getServerHandshakeResponse() != null;
    */
    private void performHandshake() {
        String handshakeMessage = ClientProtocol.HELLO.toString() +
                ClientProtocol.SEPARATOR +
                "Go Game Client" +
                ClientProtocol.SEPARATOR +
                ClientProtocol.CHAT +
                ClientProtocol.SEPARATOR +
                ClientProtocol.RANK +
                ClientProtocol.SEPARATOR +
                ClientProtocol.NAMEDQUEUES +
                ClientProtocol.SEPARATOR +
                ClientProtocol.CHALLENGE;

        Lock handshakeLock = gameClient.getHandshakeLock();
        handshakeLock.lock();
        try {
            gameClient.sendServerMessage(handshakeMessage);
            while (gameClient.getServerHandshakeResponse() == null) {
                gameClient.getHandshakeCondition().await();
            }

            validateHandshakeResponse(gameClient.getServerHandshakeResponse().split(String.valueOf(ClientProtocol.SEPARATOR)));
            gameClient.setServerHandshakeResponse(null);
            gameClient.setSetUp(false);
        } catch (InterruptedException e) {
            handleError("Handshake interrupted");
        } finally {
            handshakeLock.unlock();
        }
    }

    /**
     * Validates the server's handshake response.
     *
     * @param components The components of the server's handshake response.
     *
     * @throws IllegalArgumentException if the server response is invalid
     */
    /*@ requires components != null;
      @ ensures components.length > 0;
      @ assignable \nothing;
    */
    private void validateHandshakeResponse(String[] components) {
        if (components.length < 2 || !components[0].equals(ClientProtocol.HELLO.toString())) {
            handleError("Invalid server response during handshake");
        }
    }

    /**
     * Prompts the user to set their username and checks for server confirmation.
     *
     */
    /*@ requires gameClient != null;
      @ ensures gameClient.getUsername() != null;
      @ assignable gameClient;
    */
    private void setUsername() {
        while (true) {
            System.out.print("Enter username: ");
            String username = scanner.nextLine();

            Lock usernameLock = gameClient.getHandshakeLock();
            usernameLock.lock();
            try {
                gameClient.sendUsername(username);
                while (gameClient.getServerHandshakeResponse() == null) {
                    gameClient.getHandshakeCondition().await();
                }

                String response = gameClient.getServerHandshakeResponse();
                if (response.equals(ClientProtocol.LOGIN.toString())) {
                    gameClient.setSetUsername(false);
                    gameClient.setUsername(username);
                    gameClient.setServerHandshakeResponse(null);
                    return;
                } else if (response.equals(ClientProtocol.ALREADYLOGGEDIN.toString())) {
                    System.out.println("Username " + username + " is already taken");
                } else {
                    handleError("Invalid server response during login");
                }
                gameClient.setServerHandshakeResponse(null);
            } catch (InterruptedException e) {
                handleError("Username setup interrupted");
            } finally {
                usernameLock.unlock();
            }
        }
    }

    /**
     * Handles any errors by displaying the error message and exiting the program.
     *
     * @param message The error message to display
     */
    /*@ requires message != null;
      @ assignable \nothing;
    */
    private void handleError(String message) {
        System.out.println("Error: " + message);
        System.exit(1);
    }

    /**
     * Main game loop that handles game state, user input, and communication with the server.
     */
    public void runTUI() {
        handshakeInitialization();
        System.out.println(GREEN_BOLD + "Connected to server successfully!" + RESET);
        String command = "";

        while (true) {
            if (gameClient.getShowMenu()) {
                printMainMenu();
                command = scanner.nextLine();
                if (!handleMainMenuCommand(command)) {
                    break;
                }
            } else if (gameClient.getShowGame()) {
                if (!gameClient.getIsPlayerInGame()) {
                    printQueueMenu();
                    command = scanner.nextLine();
                    if (!handleQueueCommand(command)) {
                        break;
                    }
                } else {
                    handleGameState();
                }
            } else if (gameClient.getShowChallenge()) {
                printChallengeMenu();
                command = scanner.nextLine();
                if (!handleChallengeMenuCommand(command)) {
                    break;
                }
            }
        }

        cleanup();
    }

    /**
     * Handles the game state during a player's turn, displaying the current game board,
     * handling player moves (human or AI), and processing opponent moves.
     */
    /*@ requires gameClient != null;
      @ ensures gameClient.getIsGameOver() == true || gameClient.getIsPlayerTurn() == false;
    */
    private void handleGameState() {
        // Check if game is over first
        if (gameClient.getIsGameOver()) {
            String winner = gameClient.getWinner();
            System.out.println("\nGame Over! Winner: " + winner);
            System.out.println("\nThe Final Game Board:");
            System.out.println(gameClient.getCurrentGameBoard().toString());
            if (winner.equals(gameClient.getUsername())) {
                System.out.println("\nCongratulations! You won!");
            } else {
                System.out.println("\nBetter luck next time!");
            }
            System.out.println("\nPress Enter to return to main menu...");
            scanner.nextLine();
            gameClient.resetGame();
            return;
        }

        // Show current game state
        Board board = gameClient.getCurrentGameBoard();
        System.out.println("\nCurrent Board:");
        System.out.println(board.toString());
        System.out.println("You are playing as: " + gameClient.getPlayerStone());
        System.out.println("Playing against: " + gameClient.getOpponentName());

        try {
            Thread.sleep(200);
        } catch (InterruptedException e) {
            System.out.println("The thread is forced out of sleep.");
        }

        if (gameClient.getIsPlayerTurn() && !gameClient.getIsGameOver()) {
            switch (this.currentPlayerType) {
                case humanPlayer:
                    handleHumanMove();
                    break;
                case naiveAI:
                    handleNaiveAIMove();
                    break;
                case mediumAI:
                    handleMediumAIMove();
                    break;
                default:
                    handleHumanMove();
                    break;
            }
        } else {
            handleOpponentMove();
        }
    }

    /**
     * Handles a naive AI player's move.
     * The AI randomly selects an available spot on the board and makes a move.
     */
    /*@ requires gameClient != null && gameClient.getCurrentGameBoard() != null;
      @ ensures gameClient.getCurrentGameBoard().isEmptyField(\old(gameClient.getCurrentGameBoard().getRandomEmptySpot()));
    */
    public void handleNaiveAIMove() {
        System.out.println("\nNaive AI turn.");
        gameClient.getGameLock().lock();
        try {
            Random rand = new Random();
            List<Integer> availablePositions = gameClient.getCurrentGameBoard().getEmptySpots();
            int boardIndex = availablePositions.get(rand.nextInt(availablePositions.size()));
            gameClient.getCurrentGameBoard().setField(boardIndex, gameClient.getPlayerStone());
            gameClient.sendMove(boardIndex);
            // Wait for server confirmation
            while (gameClient.getReceivedMove() == -1) {
                gameClient.getGameCondition().await();
            }
            gameClient.setReceivedMove(-1); // Reset for next move
            gameClient.setIsPlayerTurn(false);

        } catch (InterruptedException e) {
            System.out.println("Game was interrupted.");
        } finally {
            gameClient.getGameLock().unlock();
        }
    }

    /**
     * Handles move selection and execution for the medium difficulty AI.
     * Evaluates all possible moves and chooses the one with the highest score.
     */
    /*@ requires gameClient != null && gameClient.getCurrentGameBoard() != null;
      @ ensures \old(gameClient.getCurrentGameBoard().getEmptySpots().size()) >
           gameClient.getCurrentGameBoard().getEmptySpots().size();
      @ ensures gameClient.getIsPlayerTurn() == false;
    */
    private void handleMediumAIMove() {
        System.out.println("\nMedium AI is thinking...");
        gameClient.getGameLock().lock();
        try {
            Board board = gameClient.getCurrentGameBoard();
            List<Integer> availablePositions = board.getEmptySpots();

            if (availablePositions.isEmpty()) {
                return;
            }

            // Find best move based on scoring
            int bestScore = Integer.MIN_VALUE;
            int bestMove = availablePositions.get(0);

            for (int position : availablePositions) {
                int row = position / Board.DIM;
                int col = position % Board.DIM;
                int moveScore = evaluateMove(board, row, col);

                if (moveScore > bestScore) {
                    bestScore = moveScore;
                    bestMove = position;
                }
            }

            // Make the chosen move
            board.setField(bestMove, gameClient.getPlayerStone());
            gameClient.sendMove(bestMove);

            // Wait for server confirmation
            while (gameClient.getReceivedMove() == -1) {
                gameClient.getGameCondition().await();
            }
            gameClient.setReceivedMove(-1); // Reset for next move
            gameClient.setIsPlayerTurn(false);

        } catch (InterruptedException e) {
            System.out.println("AI move was interrupted.");
        } finally {
            gameClient.getGameLock().unlock();
        }
    }

    /**
     * Evaluates a potential move position and returns a score.
     * Higher scores indicate better moves based on multiple strategic factors.
     */
    /*@ requires board != null && row >= 0 && col >= 0;
      @ requires row < Board.DIM && col < Board.DIM;
      @ requires board.isField(row, col);
      @ ensures \result >= Integer.MIN_VALUE;
      @ ensures \result == countLiberties(board, row, col) * 3 +
           (Board.DIM - Math.abs(row - Board.DIM/2) - Math.abs(col - Board.DIM/2)) +
           (canCaptureOpponent(board, row, col, gameClient.getPlayerStone(),
            gameClient.getPlayerStone() == Stone.BLACK ? Stone.WHITE : Stone.BLACK) ? 10 : 0) +
           (movePutsUsInDanger(board, row, col, gameClient.getPlayerStone(),
            gameClient.getPlayerStone() == Stone.BLACK ? Stone.WHITE : Stone.BLACK) ? -15 : 0);
    */
    private int evaluateMove(Board board, int row, int col) {
        int score = 0;
        Stone playerStone = gameClient.getPlayerStone();
        Stone opponentStone = (playerStone == Stone.BLACK) ? Stone.WHITE : Stone.BLACK;

        // Check liberties (open adjacent spaces)
        score += countLiberties(board, row, col) * 3;

        // Check if move is near the center (generally better)
        int centerDistance = Math.abs(row - Board.DIM/2) + Math.abs(col - Board.DIM/2);
        score += (Board.DIM - centerDistance);

        // Look for moves that capture opponent stones
        if (canCaptureOpponent(board, row, col, playerStone, opponentStone)) {
            score += 10;
        }

        // Avoid moves that let opponent capture us
        if (movePutsUsInDanger(board, row, col, playerStone, opponentStone)) {
            score -= 15;
        }

        return score;
    }

    /**
     * Counts the number of liberties (empty adjacent spaces) for a position.
     */
    /*@ requires board != null && row >= 0 && col >= 0;
      @ requires row < Board.DIM && col < Board.DIM;
      @ requires board.isField(row, col);
      @ ensures \result >= 0 && \result <= 4;
      @ ensures \result == (\num_of int i; 0 <= i && i < 4;
           isValidPosition(row + directions[i][0], col + directions[i][1]) &&
           board.isEmptyField(row + directions[i][0], col + directions[i][1]));
    */
    private int countLiberties(Board board, int row, int col) {
        int liberties = 0;
        int[][] directions = {{-1,0}, {1,0}, {0,-1}, {0,1}};

        for (int[] dir : directions) {
            int newRow = row + dir[0];
            int newCol = col + dir[1];

            if (isValidPosition(newRow, newCol) && board.isEmptyField(newRow, newCol)) {
                liberties++;
            }
        }

        return liberties;
    }

    /**
     * Checks if a move would capture opponent stones by checking adjacent positions.
     */
    /*@ requires board != null && row >= 0 && col >= 0;
      @ requires row < Board.DIM && col < Board.DIM;
      @ requires board.isField(row, col);
      @ requires playerStone != null && opponentStone != null;
      @ ensures \result == (\exists int i; 0 <= i && i < 4;
           isValidPosition(row + directions[i][0], col + directions[i][1]) &&
           board.getField(row + directions[i][0], col + directions[i][1]) == opponentStone &&
           wouldBeCaptured(board, row + directions[i][0], col + directions[i][1], opponentStone));
    */
    private boolean canCaptureOpponent(Board board, int row, int col, Stone playerStone, Stone opponentStone) {
        int[][] directions = {{-1,0}, {1,0}, {0,-1}, {0,1}};

        for (int[] dir : directions) {
            int newRow = row + dir[0];
            int newCol = col + dir[1];

            if (isValidPosition(newRow, newCol) && board.getField(newRow, newCol) == opponentStone) {
                // Check if the opponent stone would be captured
                if (wouldBeCaptured(board, newRow, newCol, opponentStone)) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * Checks if placing a stone would put it in danger of capture by simulating the move.
     */
    /*@ requires board != null && row >= 0 && col >= 0;
      @ requires row < Board.DIM && col < Board.DIM;
      @ requires board.isField(row, col);
      @ requires playerStone != null && opponentStone != null;
      @ ensures board.getField(row, col) == Stone.EMPTY;
      @ ensures \result == wouldBeCaptured(board, row, col, playerStone);
    */
    private boolean movePutsUsInDanger(Board board, int row, int col, Stone playerStone, Stone opponentStone) {
        // Temporarily place our stone
        board.setField(row, col, playerStone);

        // Check if it would be captured
        boolean inDanger = wouldBeCaptured(board, row, col, playerStone);

        // Reset the position
        board.setField(row, col, Stone.EMPTY);

        return inDanger;
    }

    /**
     * Checks if a stone at given position would be captured by checking for liberties.
     */
    /*@ requires board != null && row >= 0 && col >= 0;
      @ requires row < Board.DIM && col < Board.DIM;
      @ requires board.isField(row, col);
      @ requires stone != null;
      @ ensures \result == !(\exists int i; 0 <= i && i < 4;
           isValidPosition(row + directions[i][0], col + directions[i][1]) &&
           board.isEmptyField(row + directions[i][0], col + directions[i][1]));
    */
    private boolean wouldBeCaptured(Board board, int row, int col, Stone stone) {
        int[][] directions = {{-1,0}, {1,0}, {0,-1}, {0,1}};

        for (int[] dir : directions) {
            int newRow = row + dir[0];
            int newCol = col + dir[1];

            if (isValidPosition(newRow, newCol) && board.isEmptyField(newRow, newCol)) {
                return false; // Has at least one liberty
            }
        }

        return true; // No liberties found
    }

    /**
     * Checks if a position is within the board boundaries.
     */
    /*@ requires true;
      @ ensures \result == (row >= 0 && row < Board.DIM && col >= 0 && col < Board.DIM);
      @ pure
    */
    private boolean isValidPosition(int row, int col) {
        return row >= 0 && row < Board.DIM && col >= 0 && col < Board.DIM;
    }

    /**
     * Handles a human player's move.
     * Prompts the user for input and updates the game board if the move is valid.
     */
    /*@ requires gameClient != null && gameClient.getCurrentGameBoard() != null;
      @ ensures gameClient.getCurrentGameBoard().isEmptyField(\old(gameClient.getCurrentGameBoard().getSelectedSpot()));
    */
    private void handleHumanMove() {
        System.out.println("\nIt's your turn!");
        System.out.println("Enter move as 'row,column' (e.g., '3,4'): ");
        System.out.println("* For a random valid move enter 'hint' and press enter *");
        System.out.println("To send a global message enter 'global' and press enter ");
        System.out.println("To send a targeted message enter 'targeted' and press enter ");

        while (true) {
            String command = scanner.nextLine();
            if (validateMoveInput(command)) {
                String[] coordinates = command.split(",");
                int row = Integer.parseInt(coordinates[0].trim());
                int col = Integer.parseInt(coordinates[1].trim());
                int movePosition = (row - 1) * Board.DIM + (col - 1);

                gameClient.getGameLock().lock();
                try {
                    Board currentBoard = gameClient.getCurrentGameBoard();
                    if (currentBoard.isEmptyField(row - 1, col - 1)) {
                        // Place the player's stone first
                        currentBoard.setField(movePosition, gameClient.getPlayerStone());
                        // Send move to server
                        gameClient.sendMove(movePosition);
                        // Wait for server confirmation
                        while (gameClient.getReceivedMove() == -1) {
                            gameClient.getGameCondition().await();
                        }
                        gameClient.setReceivedMove(-1); // Reset for next move
                        gameClient.setIsPlayerTurn(false);
                        break;
                    } else {
                        System.out.println("That position is already occupied. Try again.");
                    }
                } catch (InterruptedException e) {
                    System.out.println("Game was interrupted.");
                } finally {
                    gameClient.getGameLock().unlock();
                }
            } else {
                if (!activateHint && !sendMessage) {
                    System.out.println("Invalid input format. Use 'row,column' (e.g., '3,4')");
                } else {
                    Random rand = new Random();
                    List<Integer> availablePositions = gameClient.getCurrentGameBoard().getEmptySpots();
                    int boardIndex = availablePositions.get(rand.nextInt(availablePositions.size()));
                    int row = boardIndex / Board.DIM;
                    int col = boardIndex % Board.DIM;
                    System.out.println("*Hint* a valid random move is: <row> = " + (row + 1) + " <col> = " + (col + 1));
                    activateHint = false;
                    sendMessage = false;
                }
            }
        }
    }

    /**
     * Handles the opponent's move by waiting for the opponent's action.
     */
    /*@ requires gameClient != null;
      @ ensures gameClient.getIsPlayerTurn() == true;
    */
    private void handleOpponentMove() {
        System.out.println("\nWaiting for opponent's move...");
        gameClient.getGameLock().lock();
        try {
            while (!gameClient.getIsPlayerTurn() && !gameClient.getIsGameOver() && gameClient.getReceivedMove() == -1) {
                gameClient.getGameCondition().await();
            }
            gameClient.setReceivedMove(-1);
            gameClient.setIsPlayerTurn(true);
        } catch (InterruptedException e) {
            System.out.println("Game was interrupted!");
        } finally {
            gameClient.getGameLock().unlock();
        }
    }

    /**
     * Validates the format of the move input by the player.
     *
     * @param input The input string containing the coordinates.
     * @return true if the input is valid, otherwise false.
     */
    /*@ requires input != null;
      @ ensures \result == (input.matches("\\d+\\,\\d+"));
    */
    private boolean validateMoveInput(String input) {
        if (input == null || input.trim().isEmpty()) {
            return false;
        }

        if (input.equals("hint")) {
            activateHint = true;
            return false;
        }

        if (input.equals("global")) {
            handleGlobalMessageSending();
            sendMessage = true;
            return false;
        }

        if (input.equals("targeted")) {
            handleTargetedMessageSending();
            sendMessage = true;
            return false;
        }

        String[] parts = input.split(",");
        if (parts.length != 2) {
            return false;
        }

        try {
            int row = Integer.parseInt(parts[0].trim());
            int col = Integer.parseInt(parts[1].trim());

            // Check if coordinates are within board bounds (7x7 board)
            return row >= 1 && row <= Board.DIM && col >= 1 && col <= Board.DIM;
        } catch (NumberFormatException e) {
            return false;
        }
    }

    /**
     * Prints the main menu to the user.
     */
    /*@ requires gameClient != null;
      @ assignable \nothing;
    */
    private void printMainMenu() {
        System.out.println(GREEN_BOLD + "\n=== Go Game Menu ===");
        System.out.println("1. List all players");
        System.out.println("2. Message all players that have access to a chat");
        System.out.println("3. Message targeted player that has access to a chat");
        System.out.println("4. Join game queue as a human");
        System.out.println("5. Join game queue as a naive AI");
        System.out.println("6. Join game queue as a medium AI");
        System.out.println("7. Join game named queue as a medium AI");
        System.out.println("8. Join game named queue as a medium AI");
        System.out.println("9. Join game named queue as a medium AI");
        System.out.println("10. Print this help menu");
        System.out.println("11. Get the ranks of players on the server");
        System.out.println("12. Challenge an opponent to a game");
        System.out.println("0. Quit");
        System.out.print("Enter your choice: " + RESET);
    }

    private void printChallengeMenu() {
        System.out.println(GREEN_BOLD + "\n=== Challenge ===");
        System.out.println("Player " + gameClient.getChallengerName() + " has challenged you to a game.");
        System.out.println("Answer: ");
        System.out.println("\t1. Accept");
        System.out.println("\t2. Reject");
        System.out.print("Enter your choice: " + RESET);
    }

    private void handleChallengeOpponentToAGame() {
        this.currentPlayerType = humanPlayer;
        System.out.print("Please enter the name of the opponent: ");
        String opponentName = scanner.nextLine();
        this.gameClient.setIsPlayerInChallengeQueue(true);
        this.gameClient.sendServerMessage(ClientProtocol.CHALLENGE.toString() + ClientProtocol.SEPARATOR + opponentName);
        this.gameClient.getChallengeLock().lock();
        System.out.println("Waiting the response from " + opponentName);
        try {
            while (!this.gameClient.getChallengeResponded()) {
                this.gameClient.getChallengeCondition().await();
            }
        } catch (InterruptedException e) {
            System.out.println("Challenge Interrupted");
        } finally {
            this.gameClient.getChallengeLock().unlock();
        }
        this.gameClient.setChallengeResponded(false);
    }

    /**
     * Prints the queue menu to the user.
     */
    /*@ requires gameClient != null;
      @ assignable \nothing;
    */
    private void printQueueMenu() {
        System.out.println(GREEN_BOLD + "\n=== Queue Menu ===");
        if (this.isNamedQueue) {
            System.out.println("*** Queue name: " + this.namedQueue + " ***");
        }
        System.out.print("You are currently in the game queue as a ");
        switch (this.currentPlayerType) {
            case humanPlayer:
                System.out.println("human player.");
                break;
            case naiveAI:
                System.out.println("naive ai.");
                break;
            case mediumAI:
                System.out.println("medium ai.");
                break;
            default:
                System.out.println("human player.");
                break;
        }
        System.out.println("2. Leave queue");
        System.out.println("0. Quit");
        System.out.print("Enter your choice: " + RESET);
    }

    /**
     * Handles the main menu commands selected by the user.
     */
    /*@ requires command != null;
      @ ensures \result == true || \result == false;
      @ assignable \nothing;
    */
    private boolean handleMainMenuCommand(String command) {
        try {
            int choice = Integer.parseInt(command);
            switch (choice) {
                case 0:
                    return false; // Quit
                case 1:
                    gameClient.sendServerMessage(ClientProtocol.LIST.toString());
                    return true;
                case 2:
                    handleGlobalMessageSending();
                    return true;
                case 3:
                    handleTargetedMessageSending();
                    return true;
                case 4:
                    setQueueSettings();
                    this.currentPlayerType = humanPlayer;
                    return true;
                case 5:
                    setQueueSettings();
                    this.currentPlayerType = naiveAI;
                    return true;
                case 6:
                    setQueueSettings();
                    this.currentPlayerType = mediumAI;
                    return true;
                case 7:
                    this.isNamedQueue = true;
                    setQueueSettings();
                    this.currentPlayerType = humanPlayer;
                    return true;
                case 8:
                    this.isNamedQueue = true;
                    setQueueSettings();
                    this.currentPlayerType = naiveAI;
                    return true;
                case 9:
                    this.isNamedQueue = true;
                    setQueueSettings();
                    this.currentPlayerType = mediumAI;
                    return true;
                case 10:
                    printMainMenu();
                    return true;
                case 11:
                    handleGetRanks();
                    return true;
                case 12:
                    handleChallengeOpponentToAGame();
                    return true;
                default:
                    System.out.println("Invalid option. Please try again.");
                    return true;
            }
        } catch (NumberFormatException e) {
            System.out.println("Please enter a valid number.");
            return true;
        }
    }

    private boolean handleChallengeMenuCommand(String command) {
        try {
            int choice = Integer.parseInt(command);
            switch (choice) {
                case 1:
                    handleAcceptChallenge();
                    return true;
                case 2:
                    handleRejectChallenge();
                    return true;
                default:
                    System.out.println("Invalid option. Please try again.");
                    return true;
            }
        } catch (NumberFormatException e) {
            System.out.println("Please enter a valid number.");
            return true;
        }
    }

    private void handleGlobalMessageSending() {
        System.out.print("Type your message: ");
        String message = scanner.nextLine();
        gameClient.sendServerMessage(ClientProtocol.CHAT.toString() +
                                             ClientProtocol.SEPARATOR +
                                             message);
    }

    private void handleTargetedMessageSending() {
        System.out.print("Enter the username of player you want to message: ");
        String target = scanner.nextLine();
        System.out.print("Enter the message: ");
        String message = scanner.nextLine();
        gameClient.sendServerMessage(ClientProtocol.WHISPER.toString() +
                                             ClientProtocol.SEPARATOR +
                                             target +
                                             ClientProtocol.SEPARATOR +
                                             message);
    }

    private void handleAcceptChallenge() {
        this.gameClient.setShowChallenge(false);
        this.gameClient.setShowGame(true);
        this.gameClient.setShowMenu(false);
        this.gameClient.sendServerMessage(ClientProtocol.ACCEPT.toString() +
                                                  ClientProtocol.SEPARATOR +
                                                  gameClient.getChallengerName());
        this.gameClient.setChallengerName(null);
        this.currentPlayerType = humanPlayer;
    }

    private void handleRejectChallenge() {
        this.gameClient.setShowChallenge(false);
        this.gameClient.setShowMenu(true);
        this.gameClient.sendServerMessage(ClientProtocol.REJECT.toString() +
                                                  ClientProtocol.SEPARATOR +
                                                  gameClient.getChallengerName());
        this.gameClient.setChallengerName(null);
        this.currentPlayerType = IDLE_STATE;
    }

    /**
     * Configures queue settings when a player joins the queue.
     */
    /*@ requires gameClient != null;
      @ ensures gameClient.getIsPlayerQueued() == true;
    */
    private void setQueueSettings() {
        gameClient.setShowMenu(false);
        gameClient.setShowGame(true);
        gameClient.setIsPlayerQueued(true);
        if (this.isNamedQueue) {
            System.out.print("Please enter the name of the wanted queue: ");
            this.namedQueue = scanner.nextLine();
            gameClient.sendServerMessage(ClientProtocol.QUEUE.toString() +
                                                 ClientProtocol.SEPARATOR + this.namedQueue);
        } else {
            gameClient.sendServerMessage(ClientProtocol.QUEUE.toString());
        }
    }

    /**
     * Handles commands related to the game queue.
     */
    /*@ requires command != null;
      @ ensures \result == true || \result == false;
      @ assignable \nothing;
    */
    private boolean handleQueueCommand(String command) {
        try {
            int choice = Integer.parseInt(command);
            switch (choice) {
                case 0:
                    return false; // Quit
                case 2:
                    if (!gameClient.getIsPlayerInGame()) {
                        gameClient.setShowMenu(true);
                        gameClient.setShowGame(false);
                        gameClient.setIsPlayerQueued(false);
                        this.currentPlayerType = IDLE_STATE;
                        if (this.isNamedQueue) {
                            gameClient.sendServerMessage(ClientProtocol.QUEUE.toString() +
                                                                 ClientProtocol.SEPARATOR +
                                                                 namedQueue);
                            this.isNamedQueue = false;
                            namedQueue = null;
                        } else {
                            gameClient.sendServerMessage(ClientProtocol.QUEUE.toString());
                        }
                    }
                    return true;
                default:
                    System.out.println("Invalid option. Please try again.");
                    return true;
            }
        } catch (NumberFormatException e) {
            System.out.println("Please enter a valid number.");
            return true;
        }
    }

    private void handleGetRanks() {
        gameClient.sendServerMessage(ClientProtocol.RANK.toString());
    }

    /**
     * Cleans up resources and exits the game.
     */
    /*@ requires gameClient != null;
      @ ensures gameClient.getIsGameOver() == true;
    */
    private void cleanup() {
        System.out.println("\nExiting game...");
        if (gameClient != null) {
            gameClient.removeListener(this);
            gameClient.close();
        }
        scanner.close();
    }

    /**
     * The main function activates the CLI.
     * @param args CLA
     */
    public static void main(String[] args) {
        new GoGameClientTUI().runTUI();
    }
}