package ss.week2.p2_3_to_8;

import java.util.Scanner;

public class ThreeWayLampTUI {
    private ThreeWayLamp lamp;
    private TUIOptions option;

    /*@
        private invariant lamp != null;
        private invariant option != null;
    */

    /**
     * The constructor for ThreeWayLampTUI calls the ThreeWayLamp Constructor to create the required
     * object.
     * The constructor initializes the option enum to off.
     */
    public ThreeWayLampTUI() {
        this.lamp = new ThreeWayLamp();
        this.option = TUIOptions.OFF;
    }

    /**
     * Prints the options menu for the lamp to the standard output.
     */
    /*@
        requires this.lamp != null;
        requires this.option != null;
        ensures this.lamp != null;
        ensures this.option != null;
    */
    public void printMenu() {
        System.out.println("Hello user!");
        System.out.println("These are the available options:");
        System.out.println("1. OFF");
        System.out.println("2. LOW");
        System.out.println("3. MEDIUM");
        System.out.println("4. HIGH");
        System.out.println("5. STATE");
        System.out.println("6. NEXT");
        System.out.println("7. HELP");
        System.out.println("0. EXIT");
    }

    public static byte getUserInput() {
        Scanner scanner = new Scanner(System.in);
        while (true) {
            try {
                System.out.print("Please choose one of the following options from 0 to 7 and by enter:");
                String input = scanner.nextLine();
                byte option = Byte.parseByte(input);
                return option;
            } catch (NumberFormatException e) {
                System.out.println("Invalid option! Please try again.");
            }
        }
    }

    private void setOption(byte option) {
        this.option = switch (option) {
            case 0 -> TUIOptions.EXIT;
            case 1 -> TUIOptions.OFF;
            case 2 -> TUIOptions.LOW;
            case 3 -> TUIOptions.MEDIUM;
            case 4 -> TUIOptions.HIGH;
            case 5 -> TUIOptions.STATE;
            case 6 -> TUIOptions.NEXT;
            case 7 -> TUIOptions.HELP;
            default -> TUIOptions.HELP;
        };
    }

    private void executeUserOption() {
        switch (this.option) {
            case OFF:
                this.lamp.setLampOFF();
                break;
            case LOW:
                this.lamp.setLampLOW();
                break;
            case MEDIUM:
                this.lamp.setLampMEDIUM();
                break;
            case HIGH:
                this.lamp.setLampHIGH();
                break;
            case STATE:
                System.out.println(lamp.getCurrentLampState());
                break;
            case NEXT:
                this.lamp.setNextSetting();
                break;
            case HELP:
                printMenu();
                break;
            default:
                printMenu();
                break;
        }
    }

    private void run() {
        // Let the user know their options
        printMenu();

        while (true) {
            // Get user's input
            byte userInput = getUserInput();
            setOption(userInput);
            System.out.println(this.option.getCommandConfirmation());
            if (this.option.equals(TUIOptions.EXIT)) {
                break;
            }
            executeUserOption();
        }
    }

    public static void main(String[] args) {
        ThreeWayLampTUI tui = new ThreeWayLampTUI();
        tui.run();
    }
}
