package ss.week2.ECK;

import ss.week2.ECK.PairOfDice;
import ss.week2.ECK.StatCalc;

public class DiceRollSimulation {
    public static void main(String[] args) {
        // Create PairOfDice object
        PairOfDice dice = new PairOfDice();

        // Iterate through all possible totals (2 to 12)
        for (int total = 2; total <= 12; total++) {
            StatCalc stats = new StatCalc();

            // Perform the experiment 10,000 times for the current total
            for (int trial = 0; trial < 10000; trial++) {
                int rolls = 0;
                int sum;

                // Roll the dice until the desired total is reached
                do {
                    dice.roll();
                    sum = dice.getTotal();
                    rolls++;
                } while (sum != total);

                // Add the number of rolls to the statistics calculator
                stats.enter(rolls);
            }

            // Report the results for the current total
            System.out.printf("Total %2d: Avg = %.2f, StdDev = %.2f, Max = %.2f%n",
                              total, stats.getMean(), stats.getStandardDeviation(), stats.getMax());
        }
    }
}
