package ss.TikTakToe;

/**
 * Records the name of the player and allows choosing a move via an abstract
 * method Move determineMove(Game game) that depends on the kind of player,
 * e.g., a human player or a computer player.
 */
public abstract class AbstractPlayer implements Player {
    protected String name;
    protected Mark playerMark;
    abstract public Mark getPlayerMark();
    abstract public Move determineMove(Game game);
    abstract public String getName();
}
