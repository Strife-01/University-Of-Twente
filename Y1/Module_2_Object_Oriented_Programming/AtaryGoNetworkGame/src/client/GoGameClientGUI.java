package client;

import client.protocol.ClientProtocol;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import javafx.scene.shape.Circle;
import javafx.stage.Stage;
import game.utils.Stone;
import game.implementations.Board;

public class GoGameClientGUI extends Application implements ClientListener {
    private GoGameClient gameClient;
    private Stage primaryStage;
    private Scene connectionScene;
    private Scene gameScene;
    private GridPane boardGrid;
    private Label statusLabel;
    private VBox gameStateBox;
    private Button queueButton;
    private ListView<String> playerListView;
    private boolean isInGame = false;

    @Override
    public void start(Stage primaryStage) {
        this.primaryStage = primaryStage;
        primaryStage.setTitle("Go Game Client");

        createConnectionScene();
        primaryStage.setScene(connectionScene);
        primaryStage.show();
    }

    private void createConnectionScene() {
        VBox connectionBox = new VBox(10);
        connectionBox.setPadding(new Insets(20));
        connectionBox.setAlignment(Pos.CENTER);

        TextField hostField = new TextField("localhost");
        hostField.setPromptText("Server Address");
        TextField portField = new TextField("8888");
        portField.setPromptText("Port");
        TextField usernameField = new TextField();
        usernameField.setPromptText("Username");

        Button connectButton = new Button("Connect");
        Label errorLabel = new Label();
        errorLabel.setTextFill(Color.RED);

        connectButton.setOnAction(e -> {
            try {
                String host = hostField.getText();
                int port = Integer.parseInt(portField.getText());
                String username = usernameField.getText();

                gameClient = new GoGameClient(java.net.InetAddress.getByName(host), port);
                gameClient.setSetUp(true);
                gameClient.getConnection().start();

                // Perform handshake
                performHandshake(username, errorLabel);
            } catch (Exception ex) {
                errorLabel.setText("Connection failed: " + ex.getMessage());
            }
        });

        connectionBox.getChildren().addAll(
                new Label("Server Connection"),
                hostField,
                portField,
                usernameField,
                connectButton,
                errorLabel
        );

        connectionScene = new Scene(connectionBox, 400, 300);
    }

    private void performHandshake(String username, Label errorLabel) {
        new Thread(() -> {
            try {
                // Send HELLO message
                String handshakeMessage = ClientProtocol.HELLO.toString() + ClientProtocol.SEPARATOR + "Go Game Client";

                gameClient.getHandshakeLock().lock();
                try {
                    gameClient.sendServerMessage(handshakeMessage);
                    while (gameClient.getServerHandshakeResponse() == null) {
                        gameClient.getHandshakeCondition().await();
                    }

                    String response = gameClient.getServerHandshakeResponse();
                    gameClient.setServerHandshakeResponse(null);

                    if (!response.startsWith(ClientProtocol.HELLO.toString())) {
                        throw new Exception("Invalid handshake response");
                    }
                } finally {
                    gameClient.getHandshakeLock().unlock();
                }

                // Send username
                gameClient.getHandshakeLock().lock();
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

                        Platform.runLater(() -> {
                            createGameScene();
                            primaryStage.setScene(gameScene);
                            gameClient.addListener(this);
                        });
                    } else if (response.equals(ClientProtocol.ALREADYLOGGEDIN.toString())) {
                        Platform.runLater(() -> errorLabel.setText("Username already taken"));
                    }
                } finally {
                    gameClient.getHandshakeLock().unlock();
                }
            } catch (Exception e) {
                Platform.runLater(() -> errorLabel.setText("Connection error: " + e.getMessage()));
            }
        }).start();
    }

    private void createGameScene() {
        BorderPane root = new BorderPane();

        // Create the game board
        createBoardGrid();

        // Create the game state panel
        createGameStatePanel();

        // Create the player list
        createPlayerList();

        // Layout
        root.setCenter(boardGrid);
        root.setRight(gameStateBox);

        gameScene = new Scene(root, 800, 600);
    }

    private void createBoardGrid() {
        boardGrid = new GridPane();
        boardGrid.setAlignment(Pos.CENTER);
        boardGrid.setHgap(2);
        boardGrid.setVgap(2);
        boardGrid.setPadding(new Insets(20));

        // Create 7x7 board
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                StackPane cell = createBoardCell(i, j);
                boardGrid.add(cell, j, i);
            }
        }
    }

    private StackPane createBoardCell(int row, int col) {
        StackPane cell = new StackPane();
        cell.setStyle("-fx-background-color: #E6C388; -fx-border-color: black;");
        cell.setPrefSize(60, 60);

        final int finalRow = row;
        final int finalCol = col;

        cell.setOnMouseClicked(e -> {
            if (gameClient.getIsPlayerTurn() && !gameClient.getIsGameOver()) {
                handleMove(finalRow, finalCol);
            }
        });

        return cell;
    }

    private void handleMove(int row, int col) {
        gameClient.getGameLock().lock();
        try {
            Board currentBoard = gameClient.getCurrentGameBoard();
            if (currentBoard.isEmptyField(row, col)) {
                int movePosition = row * Board.DIM + col;
                currentBoard.setField(movePosition, gameClient.getPlayerStone());
                gameClient.sendMove(movePosition);

                // Wait for server confirmation
                while (gameClient.getReceivedMove() == -1) {
                    gameClient.getGameCondition().await();
                }
                gameClient.setReceivedMove(-1);
                gameClient.setIsPlayerTurn(false);
                updateBoard();
                updateGameState();
            }
        } catch (InterruptedException ex) {
            ex.printStackTrace();
        } finally {
            gameClient.getGameLock().unlock();
        }
    }

    private void createGameStatePanel() {
        gameStateBox = new VBox(10);
        gameStateBox.setPadding(new Insets(20));
        gameStateBox.setPrefWidth(200);

        statusLabel = new Label();
        queueButton = new Button("Join Queue");
        queueButton.setOnAction(e -> handleQueueButton());

        Button listPlayersButton = new Button("List Players");
        listPlayersButton.setOnAction(e -> gameClient.sendServerMessage(ClientProtocol.LIST.toString()));

        Button exitButton = new Button("Exit");
        exitButton.setOnAction(e -> handleExit());

        gameStateBox.getChildren().addAll(
                statusLabel,
                queueButton,
                listPlayersButton,
                exitButton
        );
    }

    private void createPlayerList() {
        playerListView = new ListView<>();
        playerListView.setPrefHeight(200);
        gameStateBox.getChildren().add(playerListView);
    }

    private void handleQueueButton() {
        if (!gameClient.getIsPlayerQueued()) {
            gameClient.setShowMenu(false);
            gameClient.setShowGame(true);
            gameClient.setIsPlayerQueued(true);
            gameClient.sendServerMessage(ClientProtocol.QUEUE.toString());
            queueButton.setText("Leave Queue");
        } else if (!gameClient.getIsPlayerInGame()) {
            gameClient.setShowMenu(true);
            gameClient.setShowGame(false);
            gameClient.setIsPlayerQueued(false);
            gameClient.sendServerMessage(ClientProtocol.QUEUE.toString());
            queueButton.setText("Join Queue");
        }
    }

    private void updateBoard() {
        Platform.runLater(() -> {
            Board board = gameClient.getCurrentGameBoard();
            for (int i = 0; i < Board.DIM; i++) {
                for (int j = 0; j < Board.DIM; j++) {
                    StackPane cell = (StackPane) boardGrid.getChildren().get(i * Board.DIM + j);
                    cell.getChildren().clear();

                    Stone stone = board.getField(i, j);
                    if (stone != null) {
                        Circle circle = new Circle(25);
                        circle.setFill(stone == Stone.BLACK ? Color.BLACK : Color.WHITE);
                        circle.setStroke(Color.BLACK);
                        cell.getChildren().add(circle);
                    }
                }
            }
        });
    }

    private void updateGameState() {
        Platform.runLater(() -> {
            if (gameClient.getIsGameOver()) {
                String winner = gameClient.getWinner();
                statusLabel.setText("Game Over!\nWinner: " + winner);
                queueButton.setText("Join Queue");
                queueButton.setDisable(false);
            } else if (gameClient.getIsPlayerInGame()) {
                statusLabel.setText("Playing as: " + gameClient.getPlayerStone() +
                                            "\nVs: " + gameClient.getOpponentName() +
                                            "\n" + (gameClient.getIsPlayerTurn() ? "Your turn" : "Opponent's turn"));
                queueButton.setDisable(true);
            } else if (gameClient.getIsPlayerQueued()) {
                statusLabel.setText("Waiting for opponent...");
                queueButton.setText("Leave Queue");
                queueButton.setDisable(false);
            } else {
                statusLabel.setText("Not in game");
                queueButton.setText("Join Queue");
                queueButton.setDisable(false);
            }
        });
    }

    private void handleExit() {
        if (gameClient != null) {
            gameClient.removeListener(this);
            gameClient.close();
        }
        Platform.exit();
    }

    @Override
    public void connectionLost() {
        Platform.runLater(() -> {
            Alert alert = new Alert(Alert.AlertType.ERROR, "Connection to server lost!", ButtonType.OK);
            alert.showAndWait();
            Platform.exit();
        });
    }

    public void onGameStart(String player1, String player2) {
        Platform.runLater(() -> {
            isInGame = true;
            // Set up player information
            gameClient.setPlayerStone(player1.equals(gameClient.getUsername()) ? Stone.BLACK : Stone.WHITE);
            statusLabel.setText("Game Started! " + player1 + " vs " + player2);
            queueButton.setDisable(true); // Disable the queue button once the game has started
        });
    }

    public void onMoveReceived(int position) {
        Platform.runLater(() -> {
            // Make the move on the board
            Board board = gameClient.getCurrentGameBoard();
            if (board != null) {
                // Convert position back to row and column
                int row = position / Board.DIM;
                int col = position % Board.DIM;

                // Determine the opponent's stone
                Stone opponentStone = (gameClient.getPlayerStone() == Stone.BLACK) ? Stone.WHITE : Stone.BLACK;

                // Update the board with the opponent's stone
                board.setField(position, opponentStone);

                // Update the board display
                updateBoard();
                updateGameState();
            }
        });
    }


    public static void main(String[] args) {
        launch(args);
    }
}
