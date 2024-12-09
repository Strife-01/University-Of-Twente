package ss.week1;

import java.lang.Math;
import java.util.Scanner;

public class NumberGuessor {
    public static void main(String[] args) {
        // Generate a number between 1 and 100
        byte number = (byte) (Math.random() * 100);
        // Ask the user for numbers until win.
        byte guess = -1;
        Scanner sc = new Scanner(System.in);
        System.out.print("Guess a number between 0 and 100: ");
        guess = sc.nextByte();
        long nrTries = 1;
        while (guess != number) {
            if (guess > number) {
                System.out.println("Too high! ");
            } else {
                System.out.println("Too low! ");
            }
            System.out.print("Your guess: ");
            guess = sc.nextByte();
            nrTries++;
        }
        System.out.println("Correct great job.");
        System.out.println("Number of tries: " + nrTries);
    }
}
