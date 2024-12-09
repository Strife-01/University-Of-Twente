package ss.week1;

import java.util.Scanner;

public class TaxCalculator {
    public static void main(String[] args) {
        final double STAGE_1_TAX = 35472;
        final double STAGE_1_TAX_PERCENTAGE = 0.0942;
        final double STAGE_2_TAX = 69398;
        final double STAGE_2_TAX_ADDON = 3341;
        final double STAGE_2_TAX_PERCENTAGE = 0.3707;
        final double STAGE_3_TAX_ADDON = 15917;
        final double STAGE_3_TAX_PERCENTAGE = 0.4950;

        Scanner sc = new Scanner(System.in);
        System.out.print("What is your income ? ");
        double income = sc.nextDouble();
        double tax;
        if (income <= STAGE_1_TAX) {
            tax = STAGE_1_TAX_PERCENTAGE * income;
        } else if (income <= STAGE_2_TAX) {
            tax = STAGE_2_TAX_ADDON + STAGE_2_TAX_PERCENTAGE * (income - STAGE_1_TAX);
        } else {
            tax = STAGE_3_TAX_ADDON + STAGE_3_TAX_PERCENTAGE * (income - STAGE_2_TAX);
        }

        System.out.println("Your income tax is " + tax);
    }
}
