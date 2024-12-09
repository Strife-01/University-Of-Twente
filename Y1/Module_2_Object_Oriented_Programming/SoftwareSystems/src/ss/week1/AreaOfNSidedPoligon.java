package ss.week1;

import java.util.Scanner;
import java.lang.Math;

public class AreaOfNSidedPoligon {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        // Ask the user for how many sides are there in his polygon
        System.out.print("Enter the number of sides: ");
        long n = scanner.nextLong();
        // If number is less than 1 exit
        if (n < 1) {
            System.out.println("Invalid input");
            System.exit(1);
        }
        // Ask the user for the length of one side of the regular polygon
        System.out.print("Enter the length of each side: ");
        double s = scanner.nextDouble();
        // If number is less than 0 exit
        if (s < 0) {
            System.out.println("Invalid input");
            System.exit(2);
        }
        double area = 1.0 / 4.0 * (double) (n) * Math.pow(s, 2) * (1.0 / Math.tan(Math.PI / (double)n));
        System.out.println("The area is: " + area);
    }
}
