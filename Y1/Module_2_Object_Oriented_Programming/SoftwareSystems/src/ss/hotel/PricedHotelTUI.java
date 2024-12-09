package ss.hotel;

import java.util.List;
import java.util.Scanner;
import ss.hotel.bill.StringBillPrinter;

public class PricedHotelTUI {
    private static final String IN = "in";
    private static final String OUT = "out";
    private static final String ROOM = "room";
    private static final String ACTIVATE = "activate";
    private static final String BILL = "bill";
    private static final String HELP = "help";
    private static final String PRINT = "print";
    private static final String EXIT = "exit";

    private void printOptions() {
        System.out.println("\nCommands:");
        System.out.printf(" %s name ................. check in guest with name\n", IN);
        System.out.printf(" %s name ................ check out guest with name\n", OUT);
        System.out.printf(" %s name ............... request room of guest with name\n", ROOM);
        System.out.printf(" %s name password .. activate safe , password required for PricedSafe\n", ACTIVATE);
        System.out.printf(" %s name nights ......... print bill for guest (name) and number of nights\n", BILL);
        System.out.printf(" %s .................... help (this menu)\n", HELP);
        System.out.printf(" %s ................... print state\n", PRINT);
        System.out.printf(" %s .................... exit\n", EXIT);
    }

    private String[] getUserOption() {
        Scanner scanner = new Scanner(System.in);
        while (true) {
            System.out.print("Command: ");
            String[] input = scanner.nextLine().strip().split("\\s+");
            if (input.length > 1) {
            input[1].toLowerCase();
            } else if (input.length > 0) {
                input[0].toLowerCase();
            }

            if (input.length > 3) {
                System.out.println("\n*** Please enter a valid option. ***");
                continue;
            }
            if (!validateOption(input)) {
                System.out.println("\n*** Please enter a valid option. ***");
                continue;
            }
            return input;
        }
    }

    private boolean validateOption(String[] input) {
        return switch (input[0]) {
            case ACTIVATE -> input.length == 2 || input.length == 3;
            case BILL -> input.length == 3;
            case IN, OUT, ROOM -> input.length == 2;
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
                if (r.getSafe() instanceof PricedSafe) {
                    System.out.printf("The password from this room is %s.\n" ,((PricedSafe) r.getSafe()).getPassword().getInitPass());
                } else {
                    System.out.println("This room has no PriceSafe.");
                }
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
                if (!(r instanceof PricedRoom)) {
                    r.getSafe().activate();
                    if (optionArray.length == 2) {
                        System.out.printf("Safe in room %d of guest %s is activated.\n",
                                          r.getNumber(), optionArray[1]);
                    } else {
                        System.out.println("This safe has no password please try activating without");
                    }
                } else {
                    if (optionArray.length < 3) {
                        System.out.println("Wrong params at activation ( password required )");
                        break;
                    } else {
                        try {
                            ((PricedSafe) r.getSafe()).activate(optionArray[2]);
                            if (r.getSafe().isActive()) {
                                System.out.printf("Safe in room %d of guest %s is activated.\n",r.getNumber(), optionArray[1]);
                            } else {
                                System.out.println("Wrong password");
                            }
                            break;
                        } catch (AssertionError e) {
                            System.out.println("Wrong password");
                        }
                    }
                }
                break;
            case BILL:
                if (!(hotel.getRoom(optionArray[1]) instanceof PricedRoom)) {
                    System.out.println("\nThis room cannot be billed.");
                    break;
                }
                int nrNights;
                try {
                    nrNights = Integer.parseInt(optionArray[2]);
                } catch (NumberFormatException e) {
                    System.out.println("Please enter a valid number...");
                    break;
                }
                System.out.println(((StringBillPrinter) ((PricedHotel) hotel).getBill(optionArray[1], nrNights, new StringBillPrinter()).getBillPrinter()).getResult());
                break;
            case PRINT:
                System.out.println(hotel.toString());
                break;
            case HELP:
                printOptions();
                break;
            default:
                break;
        }
    }

    private void run() {
        PricedHotel hotel = new PricedHotel("Hotel Twente");
        System.out.printf("Welcome to the Hotel management system of the \"%s\"\n",
                          hotel.getName());
        printOptions();

        while (true) {
            String[] userOption = getUserOption();
            if (userOption[0].equals(EXIT)) {
                break;
            }
            executeUserOption(userOption, hotel);
        }
    }

    public static void main(String[] args) {
        PricedHotelTUI hotelTUI = new PricedHotelTUI();
        hotelTUI.run();
    }
}
