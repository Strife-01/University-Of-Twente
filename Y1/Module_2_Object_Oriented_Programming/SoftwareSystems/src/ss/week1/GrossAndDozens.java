package ss.week1;

// imports
import java.util.Scanner;

public class GrossAndDozens {
    public static void main(String[] args) {
        final int EGGS_PER_GROSS = 144;
        final int EGGS_PER_DOZEN = 12;
        // Ask the user for the number of eggs:
        System.out.print("How many eggs do you have?");
        Scanner scanner = new Scanner(System.in);
        int eggs = scanner.nextInt();
        // Close the scanner - remove the memory it has been allocated for it
        // Makes sure that the scanner cannot be used after we don't need it anymore
        scanner.close();
        // Compute gross, dozens and left overs)
        int grosses = eggs / EGGS_PER_GROSS;
        int dozens = (eggs % (grosses * EGGS_PER_GROSS)) / EGGS_PER_DOZEN;
        int left_over_eggs = eggs - (grosses * EGGS_PER_GROSS + dozens * EGGS_PER_DOZEN);
        // Inform user about how can he compartment eggs
        System.out.println("Your number of eggs is " + grosses + " gross , " + dozens + " dozen , and " + left_over_eggs + " left over eggs!");
    }
}
