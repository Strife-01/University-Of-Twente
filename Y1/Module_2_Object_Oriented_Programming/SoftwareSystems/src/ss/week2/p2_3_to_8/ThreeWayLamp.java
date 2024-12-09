package ss.week2.p2_3_to_8;

import java.util.Scanner;

/*
    The lamp should have the following attributes:
        -state
    The lamp should have the following queries:
        +getCurrentLampState() - of type String - returns the current state of the lamp.
    The lamp should have the following commands:
        +setNextSetting() - type null - switches the current state of the lamp with the next one.
        +printCurrentState() - type null - prints the current state to the standard output.
 */

/**
 * Represents a Lamp with 3 states that the user can circularly switch between.
 */
public class ThreeWayLamp {
    private LampSetting lampSetting;

    /*@
        private invariant this.lampSetting != null;
    */

    /**
     * Constructor with no arguments.
     * Initializes the state of the Lamp to OFF.
     */
    /*@
        ensures this.lampSetting != null;
    */
    public ThreeWayLamp() {
        this.lampSetting = LampSetting.OFF;
    }

    /*@
        requires this.lampSetting != null;
        ensures \result != null;
        ensures \result == this.lampSetting;
    */
    /*@
        pure
    */
    public LampSetting getCurrentLampState() {
        return this.lampSetting;
    }

    /**
     * Sets the state for the lamp to the next state in the cycle.
     */
    /*@
        requires this.lampSetting != null;
        ensures this.lampSetting != null;
    */
    public void setNextSetting() {
        this.lampSetting = switch (this.lampSetting) {
            case LampSetting.OFF -> LampSetting.LOW;
            case LampSetting.LOW -> LampSetting.MEDIUM;
            case LampSetting.MEDIUM -> LampSetting.HIGH;
            case LampSetting.HIGH -> LampSetting.OFF;
            default -> LampSetting.OFF;
        };
    }

    /**
     * Turns off the light.
     */
    /*@
        ensures this.lampSetting == LampSetting.OFF;
    */
    public void setLampOFF() {
        this.lampSetting = LampSetting.OFF;
    }

    /**
     * Sets the light state to low.
     */
    /*@
        ensures this.lampSetting == LampSetting.LOW;
    */
    public void setLampLOW() {
        this.lampSetting = LampSetting.LOW;
    }

    /**
     * Sets the light state to medium.
     */
    /*@
        ensures this.lampSetting == LampSetting.MEDIUM;
    */
    public void setLampMEDIUM() {
        this.lampSetting = LampSetting.MEDIUM;
    }

    /**
     * Sets light state to high.
     */
    /*@
        ensures this.lampSetting == LampSetting.HIGH;
    */
    public void setLampHIGH() {
        this.lampSetting = LampSetting.HIGH;
    }

    /**
     * Prints the current setting for the lamp to the TUI. (Standard output)
     */
    /*@
        requires this.lampSetting != null;
        ensures this.lampSetting != null;
    */
    public void printCurrentState() {
        System.out.println(this.lampSetting.getDescription());
    }
}
