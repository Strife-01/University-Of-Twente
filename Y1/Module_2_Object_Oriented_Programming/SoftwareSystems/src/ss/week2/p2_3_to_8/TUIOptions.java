package ss.week2.p2_3_to_8;

public enum TUIOptions {
    OFF("The lamp has been turned off."),
    LOW("The lamp has been set to low."),
    MEDIUM("The lamp has been set to medium."),
    HIGH("The lamp has been set to high."),
    STATE("This is the current state of the lamp:"),
    NEXT("The lamp has been set to the next state."),
    HELP("Help oprion selected."),
    EXIT("Bye");

    private String commandConfirmation;

    TUIOptions(String commandConfirmation) {
        this.commandConfirmation = commandConfirmation;
    }

    public String getCommandConfirmation() {
        return commandConfirmation;
    }
}
