package ss.week2.p2_3_to_8;

/**
 * Represents all the states that the ThreeWayLamp can have.
 */
public enum LampSetting {
    OFF("Current setting: OFF."),
    LOW("Current setting: LOW"),
    MEDIUM("Current setting: MEDIUM"),
    HIGH("Current setting: HIGH");

    private String description;

    /*@
        private invariant description != null;
    */

    LampSetting(String description) {
        this.description = description;
    }

    public String getDescription() {
        return this.description;
    }
}
