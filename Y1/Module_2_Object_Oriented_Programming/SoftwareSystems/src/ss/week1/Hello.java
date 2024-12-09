package ss.week1;

// Imports
import java.util.Scanner;

/**
 * Hello World class.
 */
public class Hello {
    /**
     * Prints a greeting to the console .
     * @param args command -line arguments ; currently unused
     */
    public static void main(String [] args) {
        // ** For exercise 1 we copy the code and print Hello... to the std output
        // System.out.println("Hello ,␣world!");
        // ** For exercise 2 we can just remove 1 semicolon
        // ** For exercise 3:
        // Ask user for their name:
        Scanner sc = new Scanner(System.in);
        System.out.print("Please enter your name: ");
        String name = sc.nextLine();
        // Ask user for their age:
        System.out.print("Please enter your age: ");
        int age = sc.nextInt();
        // Greet the user:
        System.out.println("Hello, " + name + "!" + " Your age is " + age + ".");
        // For exercise 4 will throw a runtime error exception
        // Close the scanner
        sc.close();
    }
}