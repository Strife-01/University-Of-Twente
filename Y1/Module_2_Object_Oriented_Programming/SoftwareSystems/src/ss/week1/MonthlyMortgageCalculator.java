package ss.week1;

import java.util.Scanner;
import java.lang.Math;

public class MonthlyMortgageCalculator {
    public static void main(String[] args) {
        // Initializing the scanner
        Scanner sc = new Scanner(System.in);
        // Ask user for amount borrowed
        System.out.print("What is the amount borrowed ? ");
        double P = sc.nextDouble();
        if (P < 0) {
            System.out.println("You need to enter a positive number");
            System.exit(1);
        }
        // Ask user for yearly interest rate
        System.out.print("What is the yearly interest rate (in %)? ");
        double r = sc.nextDouble();
        if (r < 0) {
            System.out.println("You need to enter a positive number");
            System.exit(2);
        }
        // Ask user for number of years
        System.out.print("What is the number of years? ");
        int y = sc.nextInt();
        if (y < 0) {
            System.out.println("You need to enter a positive number");
            System.exit(3);
        }
        sc.close();
        // nr of monthly payments
        int N = y * 12;
        // r == 0 aka no interest:
        if (r == 0) {
            System.out.println("The monthly payment is " + (P / N));
            System.exit(0);
        }
        // Monthly mortgage
        r = (r / 100.0) / 12;
        int c = (int) Math.ceil((r * P) / (1 - Math.pow(1 + r, (-N))));
        // Print monthly payment
        System.out.println("The monthly payment is " + c);
    }
}
