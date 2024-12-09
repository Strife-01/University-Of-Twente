package ss.hotel;

import java.util.List;
import java.util.Scanner;

public class HotelTUI {
    private static final String IN = "in";
    private static final String OUT = "out";
    private static final String ROOM = "room";
    private static final String ACTIVATE = "activate";
    private static final String HELP = "help";
    private static final String PRINT = "print";
    private static final String EXIT = "exit";

    private void printOptions() {
        System.out.println("\nCommands:");
        System.out.printf(" %s name ................. check in guest with name\n", IN);
        System.out.printf(" %s name ................ check out guest with name\n", OUT);
        System.out.printf(" %s name ............... request room of guest with name\n", ROOM);
        System.out.printf(" %s name ........... activate safe of guest with name\n", ACTIVATE);
        System.out.printf(" %s .................... help (this menu)\n", HELP);
        System.out.printf(" %s ................... print state\n", PRINT);
        System.out.printf(" %s .................... exit\n", EXIT);
    }

    private String[] getUserOption() {
        Scanner scanner = new Scanner(System.in);
        while (true) {
            printOptions();
            System.out.print("Command: ");
            String[] input = scanner.nextLine().strip().toLowerCase().split("\\s+");

            if (input.length > 2) {
                input = sanitizeInput(input);
            }
            if (!validateOption(input)) {
                System.out.println("\n*** Please enter a valid option. ***");
                continue;
            }
            return input;
        }
    }

    private String[] sanitizeInput(String[] input) {
        String fullName = String.join(" ", List.of(input).subList(1, input.length));
        String option = input[0];
        input = new String[2];
        input[0] = option;
        input[1] = fullName;
        return input;
    }

    private boolean validateOption(String[] input) {
        return switch (input[0]) {
            case IN, OUT, ROOM, ACTIVATE -> input.length == 2;
            case HELP, PRINT, EXIT -> input.length == 1;
            default -> false;
        };
    }

    private void executeUserOption(String[] optionArray, Hotel hotel) {
        Room r;
        switch (optionArray[0]) {
            case IN:
                r = hotel.checkIn(optionArray[1]);
                if (r == null) {
                    System.out.println("Sorry, action not possible.");
                    break;
                }
                System.out.printf("Guest %s gets room %d.\n", optionArray[1], r.getNumber());
                break;
            case OUT:
                boolean status = hotel.checkOut(optionArray[1]);
                if (status) {
                    System.out.printf("Guest %s is checked out now.\n", optionArray[1]);
                    break;
                }
                System.out.printf("Guest %s doesn't have a room.\n", optionArray[1]);
                break;
            case ROOM:
                r = hotel.getRoom(optionArray[1]);
                if (r == null) {
                    System.out.printf("Guest %s is not checked in any of our rooms.\n",
                                      optionArray[1]);
                    break;
                }
                System.out.printf("Guest %s has room %d.\n", optionArray[1], r.getNumber());
                break;
            case ACTIVATE:
                r = hotel.getRoom(optionArray[1]);
                if (r == null) {
                    System.out.printf("Guest %s is not checked in any of our rooms.\n",
                                      optionArray[1]);
                    break;
                }
                r.getSafe().activate();
                System.out.printf("Safe of guest %s is activated.\n", optionArray[1]);
                break;
            case PRINT:
                System.out.println(hotel.toString());
                break;
            default: // Help is included
                break;
        }
    }

    private void run() {
        Hotel hotel = new Hotel("Hotel Twente");
        System.out.printf("Welcome to the Hotel management system of the \"%s\"\n",
                          hotel.getName());
        while (true) {
            String[] userOption = getUserOption();
            if (userOption[0].equals(EXIT)) {
                break;
            }
            executeUserOption(userOption, hotel);
        }
    }

    public static void main(String[] args) {
        HotelTUI hotelTUI = new HotelTUI();
        hotelTUI.run();
    }
}
