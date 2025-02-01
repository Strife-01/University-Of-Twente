package game.ui;

import game.implementations.Board;
import game.implementations.GoGame;
import game.implementations.GoMove;
import game.implementations.HumanPlayer;
import game.interfaces.Game;
import game.interfaces.Player;
import game.utils.Stone;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.List;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.canvas.Canvas;
import javafx.scene.canvas.GraphicsContext;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import javafx.stage.Modality;
import javafx.stage.Stage;

/**
 * A JavaFX-based graphical user interface for the Capture Go game.
 * <p>
 * This application allows players to play Capture Go against another player locally
 * or via multiplayer. The game also supports AI with selectable difficulty.
 */
public class GoGUI extends Application implements GoUI {

    private GoGame game;
    private Label statusLabel;
    private Canvas boardCanvas;
    private TextField moveInput;
    private VBox gameLayout; // Game screen layout
    private VBox menuLayout;
    private VBox thisPcLayout; // Layout for PlayerVsPlayer and PlayerVsAI
    private VBox aiDifficultyLayout; // Layout for AI difficulty selection
    private VBox multiplayerLayout; // Multiplayer configuration layout
    private VBox multiplayerOptionsLayout;
    private VBox createServerLayout; // Layout for Create Server
    private StackPane root;  // Root container to switch between views
    private double canvasSize = 400;

    /**
     * Starts the JavaFX application by initializing various layout components.
     *
     * @param primaryStage the primary stage for this application
     */
    @Override
    public void start(Stage primaryStage) {
        // Create the main menu layout
        createMainMenu();

        // Create the "This PC" layout
        createThisPcLayout();

        // Create the AI difficulty selection layout
        createAIDifficultyLayout();

        // Create the game layout
        createGameLayout();

        // Create the multiplayer options layout
        createMultiplayerOptionsLayout();

        // Create the multiplayer configuration layout
        createMultiplayerLayout();

        // Create the server layout
        createServerLayout();

        // Root layout to hold the menu and game screens
        root = new StackPane(menuLayout); // Start with the menu layout visible

        // Set up the stage
        Scene scene = new Scene(root, 600, 600);
        primaryStage.setScene(scene);
        primaryStage.setTitle("Capture Go Game");
        primaryStage.show();
    }

    /**
     * Creates the main menu layout with options to start multiplayer, play locally, or exit the game.
     */
    private void createMainMenu() {
        menuLayout = new VBox(20);
        menuLayout.setAlignment(Pos.CENTER);

        Label title = new Label("Capture Go Game");
        title.setStyle("-fx-font-size: 24px; -fx-font-weight: bold;");

        Button multiplayerButton = new Button("Multiplayer");
        multiplayerButton.setOnAction(e -> showMultiplayerOptions()); // Open multiplayer configuration window

        Button thisPcButton = new Button("This PC");
        thisPcButton.setOnAction(e -> showThisPcOptions()); // Show PlayerVsPlayer and PlayerVsAI options

        Button exitButton = new Button("Exit");
        exitButton.setOnAction(e -> Platform.exit());

        menuLayout.getChildren().addAll(title, multiplayerButton, thisPcButton, exitButton);
    }

    /**
     * Creates the "This PC" layout with options for Player vs Player and Player vs AI.
     */
    private void createThisPcLayout() {
        thisPcLayout = new VBox(20);
        thisPcLayout.setAlignment(Pos.CENTER);

        Label title = new Label("Choose Game Mode");
        title.setStyle("-fx-font-size: 20px; -fx-font-weight: bold;");

        Button playerVsPlayerButton = new Button("PlayerVsPlayer");
        playerVsPlayerButton.setOnAction(e -> showGameScreen()); // Start the game as before

        Button playerVsAIButton = new Button("PlayerVsAI");
        playerVsAIButton.setOnAction(e -> showAIDifficultySelection()); // Go to AI difficulty selection screen

        Button backButton = new Button("Back to Main Menu");
        backButton.setOnAction(e -> showMainMenu()); // Return to the main menu

        thisPcLayout.getChildren().addAll(title, playerVsPlayerButton, playerVsAIButton, backButton);
    }

    /**
     * Creates the AI difficulty selection layout.
     */
    private void createAIDifficultyLayout() {
        aiDifficultyLayout = new VBox(20);
        aiDifficultyLayout.setAlignment(Pos.CENTER);

        Label title = new Label("Select AI Difficulty");
        title.setStyle("-fx-font-size: 20px; -fx-font-weight: bold;");

        Button naiveButton = new Button("Naive");
        naiveButton.setOnAction(e -> showMainMenu()); // Return to the main menu
        Button mediumButton = new Button("Medium");
        Button hardButton = new Button("Hard");

        Button backButton = new Button("Back to Main Menu");
        backButton.setOnAction(e -> showMainMenu()); // Return to the main menu

        aiDifficultyLayout.getChildren().addAll(title, naiveButton, mediumButton, hardButton, backButton);
    }

    /**
     * Creates the game layout.
     */
    private void createGameLayout() {
        gameLayout = new VBox(10);
        gameLayout.setAlignment(Pos.CENTER);

        // Initialize players and game
        Player player1 = createPlayer(1, Stone.BLACK);
        Player player2 = createPlayer(2, Stone.WHITE);
        game = new GoGame(Board.DIM, player1, player2);

        // Initialize the board canvas
        boardCanvas = new Canvas(canvasSize, canvasSize); // A square canvas (7 * 40 pixels per line)
        GraphicsContext gc = boardCanvas.getGraphicsContext2D();
        drawGrid(gc); // Draw the initial grid

        // Input and status section
        HBox inputSection = new HBox(10);
        inputSection.setAlignment(Pos.CENTER);
        moveInput = new TextField();
        moveInput.setPromptText("Enter move (row,column)");
        Button submitButton = new Button("Submit Move");
        submitButton.setOnAction(e -> handleMove());
        inputSection.getChildren().addAll(new Label("Move:"), moveInput, submitButton);

        // Status label
        statusLabel = new Label("Welcome to the Capture Go game!");

        // Back button to return to the main menu
        Button backButton = new Button("Back to Menu");
        backButton.setOnAction(e -> showMainMenu());

        // Add everything to the game layout
        gameLayout.getChildren().addAll(boardCanvas, inputSection, statusLabel, backButton);

        // Update the board initially
        updateBoard();
    }

    private void createMultiplayerOptionsLayout() {
        multiplayerOptionsLayout = new VBox(20);
        multiplayerOptionsLayout.setAlignment(Pos.CENTER);
        multiplayerOptionsLayout.setPadding(new Insets(20));

        Label titleLabel = new Label("Multiplayer Options");
        titleLabel.setStyle("-fx-font-size: 20px; -fx-font-weight: bold;");

        Button createServerButton = new Button("Create Server");
        createServerButton.setOnAction(e -> showCreateServerPage());

        Button connectToButton = new Button("Connect to Server");
        connectToButton.setOnAction(e -> showMultiplayerConfiguration());

        Button backButton = new Button("Back to Main Menu");
        backButton.setOnAction(e -> showMainMenu());

        multiplayerOptionsLayout.getChildren().addAll(titleLabel, createServerButton, connectToButton, backButton);
    }

    /**
     * Creates the multiplayer configuration layout.
     */
    private void createMultiplayerLayout() {
        multiplayerLayout = new VBox(20);
        multiplayerLayout.setAlignment(Pos.CENTER);
        multiplayerLayout.setPadding(new Insets(20));

        Label titleLabel = new Label("Multiplayer Configuration");
        titleLabel.setStyle("-fx-font-size: 20px; -fx-font-weight: bold;");

        // Text fields for IP address and port number
        TextField ipField = new TextField();
        ipField.setPromptText("IP Address");

        TextField portField = new TextField();
        portField.setPromptText("Port Number");

        // Buttons
        Button submitButton = new Button("Submit");
        submitButton.setOnAction(e -> {
            String ipAddress = ipField.getText();
            String portNumber = portField.getText();

            if (ipAddress.isEmpty() || portNumber.isEmpty()) {
                showErrorDialog("Both fields are required!");
            } else {
                try {
                    int port = Integer.parseInt(portNumber); // Validate port number
                    // Placeholder: Replace with actual multiplayer setup
                    showConfirmationDialog("Connecting to " + ipAddress + " on port " + port);
                } catch (NumberFormatException ex) {
                    showErrorDialog("Port number must be a valid integer!");
                }
            }
        });

        Button backButton = new Button("Back");
        backButton.setOnAction(e -> showMainMenu()); // Return to the main menu

        // Layout for the text fields and buttons
        VBox fieldsLayout = new VBox(10, new Label("IP Address:"), ipField, new Label("Port Number:"), portField);
        fieldsLayout.setAlignment(Pos.CENTER);

        multiplayerLayout.getChildren().addAll(titleLabel, fieldsLayout, submitButton, backButton);
    }

    private void createServerLayout() {
        createServerLayout = new VBox(20);
        createServerLayout.setAlignment(Pos.CENTER);
        createServerLayout.setPadding(new Insets(20));

        Label titleLabel = new Label("Create Server");
        titleLabel.setStyle("-fx-font-size: 20px; -fx-font-weight: bold;");

        Label ipLabel = new Label();
        try {
            String ipAddress = InetAddress.getLocalHost().getHostAddress();
            ipLabel.setText("Your IP-address is: " + ipAddress);
        } catch (UnknownHostException e) {
            ipLabel.setText("Unable to retrieve IP address.");
        }

        TextField portField = new TextField();
        portField.setPromptText("Port (1024-65535):");

        Button createServerButton = new Button("Create Server");
        createServerButton.setOnAction(e -> {
            String portText = portField.getText();
            try {
                int port = Integer.parseInt(portText);
                if (port < 1024 || port > 65535) {
                    showErrorDialog("Port number must be between 1024 and 65535.");
                } else {
                    showConfirmationDialog("Server created on port " + port);
                }
            } catch (NumberFormatException ex) {
                showErrorDialog("Port number must be a valid integer.");
            }
        });

        Button backButton = new Button("Back to Main Menu");
        backButton.setOnAction(e -> showMainMenu());

        createServerLayout.getChildren().addAll(titleLabel, ipLabel, new Label("Port:"), portField, createServerButton, backButton);
    }

    /**
     * Handles the logic for submitting a move during the game.
     * This includes validating the move and updating the board accordingly.
     *
     * @throws IllegalArgumentException if the move is invalid (out of bounds or already occupied)
     */
    private void handleMove() {
        String input = moveInput.getText();
        try {
            String[] parts = input.split(",");
            int row = Integer.parseInt(parts[0]) - 1;
            int col = Integer.parseInt(parts[1]) - 1;

            if (!game.getBoard().isField(row, col) || !game.getBoard().isEmptyField(row, col)) {
                statusLabel.setText("Invalid move. Try again.");
            } else {
                Stone currentStone = game.getTurn().getPlayerStone();
                GoMove move = new GoMove(row, col, currentStone);
                game.doMove(move);
                updateBoard();
                if (game.isGameover()) {
                    String winnerName = game.getWinner() != null ? game.getWinner().getName() : null;
                    showGameOverDialog(winnerName); // Show game-over dialog
                } else {
                    statusLabel.setText("Next turn: " + game.getTurn().getName());
                }
            }

            //updateBoard();
        } catch (Exception e) {
            statusLabel.setText("Invalid move. Try again.");
        } finally {
            moveInput.clear();
        }
    }

    /**
     * Shows the "Game Over" dialog when the game ends, displaying the winner.
     *
     * @param winnerName the name of the winning player, or null if the game was a draw
     */
    private void showGameOverDialog(String winnerName) {
        // Create a new stage for the dialog
        Stage dialog = new Stage();
        dialog.initModality(Modality.APPLICATION_MODAL);
        dialog.setTitle("Game Over");

        // Create dialog content
        VBox dialogLayout = new VBox(20);
        dialogLayout.setAlignment(Pos.CENTER);
        dialogLayout.setPadding(new Insets(20));

        Label message = new Label("Game over! " + (winnerName != null ? winnerName + " wins!" : "It's a draw!"));
        message.setStyle("-fx-font-size: 16px;");

        Button playAgainButton = new Button("Play Again");
        playAgainButton.setOnAction(e -> {
            dialog.close();
            resetGame();
        });

        Button exitButton = new Button("Exit to Menu");
        exitButton.setOnAction(e -> {
            dialog.close();
            showMainMenu();
        });

        dialogLayout.getChildren().addAll(message, playAgainButton, exitButton);

        // Set up the scene and show the dialog
        Scene dialogScene = new Scene(dialogLayout, 300, 200);
        dialog.setScene(dialogScene);
        dialog.showAndWait();
    }

    /**
     * Resets the game to start a new match.
     */
    private void resetGame() {
        Player player1 = createPlayer(1, Stone.BLACK);
        Player player2 = createPlayer(2, Stone.WHITE);
        game = new GoGame(Board.DIM, player1, player2);
        updateBoard();
        statusLabel.setText("Welcome to the Capture Go game! \n \t\t Black's turn first");
    }

    /**
     * Draws the game grid on the canvas.
     *
     * @param gc the GraphicsContext to draw the grid
     */
    private void drawGrid(GraphicsContext gc) {
        double size = 300;
        double step = size / 6;

        gc.setStroke(Color.BLACK);
        gc.setLineWidth(1.5);

        for (int i = 0; i < Board.DIM; i++) {
            double pos = i * step + 50;
            gc.strokeLine(50, pos, size + 50, pos); // Horizontal lines
            gc.strokeLine(pos, 50, pos, size + 50); // Vertical lines
        }
    }

    /**
     * Updates the game board to reflect the latest moves and game state.
     */
    private void updateBoard() {
        GraphicsContext gc = boardCanvas.getGraphicsContext2D();
        gc.clearRect(0, 0, canvasSize, canvasSize);
        drawGrid(gc);

        List<Stone> board = game.getBoard().getBoard();
        double size = 300;
        double step = size / 6;
        double radius = step / 1.25;
        double offset = radius / 2;

        for (int i = 0; i < board.size(); i++) {
            int row = i / Board.DIM;
            int col = i % Board.DIM;

            double x = col * step - offset + 50;
            double y = row * step - offset + 50;

            Stone stone = board.get(i);
            if (stone.equals(Stone.BLACK)) {
                gc.setFill(Color.BLACK);
                gc.fillOval(x, y, radius, radius);
            } else if (stone.equals(Stone.WHITE)) {
                gc.setFill(Color.WHITE);
                gc.fillOval(x, y, radius, radius);
                gc.setStroke(Color.BLACK);
                gc.strokeOval(x, y, radius, radius);
            }
        }
    }


    /**
     * Displays an error dialog.
     */
    private void showErrorDialog(String message) {
        Stage dialog = new Stage();
        dialog.initModality(Modality.APPLICATION_MODAL);
        dialog.setTitle("Error");

        VBox layout = new VBox(10, new Label(message), new Button("OK"));
        layout.setAlignment(Pos.CENTER);
        layout.setPadding(new Insets(20));

        Scene scene = new Scene(layout, 300, 150);
        dialog.setScene(scene);

        Button okButton = (Button) layout.getChildren().get(1);
        okButton.setOnAction(e -> dialog.close());

        dialog.showAndWait();
    }

    /**
     * Displays a confirmation dialog.
     */
    private void showConfirmationDialog(String message) {
        Stage dialog = new Stage();
        dialog.initModality(Modality.APPLICATION_MODAL);
        dialog.setTitle("Confirmation");

        VBox layout = new VBox(10, new Label(message), new Button("OK"));
        layout.setAlignment(Pos.CENTER);
        layout.setPadding(new Insets(20));

        Scene scene = new Scene(layout, 300, 150);
        dialog.setScene(scene);

        Button okButton = (Button) layout.getChildren().get(1);
        okButton.setOnAction(e -> dialog.close());

        dialog.showAndWait();
    }

    /**
     * Switches to the multiplayer configuration screen.
     */
    private void showMultiplayerConfiguration() {
        root.getChildren().setAll(multiplayerLayout);
    }

    private void showMultiplayerOptions() {
        root.getChildren().setAll(multiplayerOptionsLayout);
    }

    private void showCreateServerPage() {
        root.getChildren().setAll(createServerLayout);
    }

    /**
     * Switches to the "This PC" options screen.
     */
    private void showThisPcOptions() {
        root.getChildren().setAll(thisPcLayout);
    }

    /**
     * Switches to the AI difficulty selection screen.
     */
    private void showAIDifficultySelection() {
        root.getChildren().setAll(aiDifficultyLayout);
    }

    /**
     * Switches to the game screen.
     */
    private void showGameScreen() {
        resetGame(); // Reset game state when entering the game screen
        root.getChildren().setAll(gameLayout);
    }

    /**
     * Switches to the main menu screen.
     */
    private void showMainMenu() {
        root.getChildren().setAll(menuLayout);
    }

    public static void main(String[] args) {
        launch(args);
    }

    @Override
    public void run() {
        launch();
    }

    @Override
    public Player createPlayer(int playerNumber, Stone stone) {
        String name = playerNumber == 1 ? "Black" : "White";
        return new HumanPlayer(name, stone);
    }

    @Override
    public int getValidChoice(int min, int max) {
        return min;
    }

    @Override
    public boolean askToPlayAgain(Game game) {
        return false;
    }
}

