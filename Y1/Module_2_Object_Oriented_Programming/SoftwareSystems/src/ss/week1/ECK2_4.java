package ss.week1;

import java.util.Scanner;

public class ECK2_4 {
    public static void main(String[] args) {
        final int PENNY = 1;
        final int NICKEL = 5;
        final int DIME = 10;
        final int QUARTER = 25;

        Scanner sc = new Scanner(System.in);
        System.out.print("How many pennies: ");
        int pennies = sc.nextInt();
        System.out.print("How many nickels: ");
        int nickels = sc.nextInt();
        System.out.print("How many dimes: ");
        int dimes = sc.nextInt();
        System.out.print("How many quarters: ");
        int quarters = sc.nextInt();

        double dollars = (pennies * PENNY + nickels * NICKEL + dimes * DIME + quarters * QUARTER) / 100.0;
        System.out.println(dollars);
    }
}
