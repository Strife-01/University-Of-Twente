package ss.week2.ECK;

import java.util.Scanner;

/**
 * An object of class StatCalc can be used to compute several simple statistics
 * for a set of numbers.  Numbers are entered into the dataset using
 * the enter(double) method.  Methods are provided to return the following
 * statistics for the set of numbers that have been entered: The number
 * of items, the sum of the items, the average, and the standard deviation
 */

public class StatCalc {

    private int count;   // Number of numbers that have been entered.
    private double sum;  // The sum of all the items that have been entered.
    private double squareSum;  // The sum of the squares of all the items.
    private double maxValue;
    private double minValue;

    /**
     * Add a number to the dataset.  The statistics will be computed for all
     * the numbers that have been added to the dataset using this method.
     */
    public void enter(double num) {
        if (count == 0) {
            minValue = num;
            maxValue = num;
        } else {
            if (minValue > num) {
                minValue = num;
            }
            if (maxValue < num) {
                maxValue = num;
            }
        }
        count++;
        sum += num;
        squareSum += num*num;
    }

    /**
     * Return the number of items that have been entered into the dataset.
     */
    public int getCount() {
        return count;
    }

    /**
     * Return the sum of all the numbers that have been entered.
     */
    public double getSum() {
        return sum;
    }

    /**
     * Return the average of all the items that have been entered.
     * The return value is Double.NaN if no numbers have been entered.
     */
    public double getMean() {
        return sum / count;
    }

    /**
     * Return the standard deviation of all the items that have been entered.
     * The return value is Double.NaN if no numbers have been entered.
     */
    public double getStandardDeviation() {
        double mean = getMean();
        return Math.sqrt( squareSum/count - mean*mean );
    }

    public double getMax() {
        return this.maxValue;
    }

    public double getMin() {
        return this.minValue;
    }

    public static void main(String[] args) {
        StatCalc calc; // Object to be used to process the data.
        calc = new StatCalc();
        Scanner sc = new Scanner(System.in);
        double input = 0;
        while ((input = sc.nextDouble()) != 0) {
            calc.enter(input);
        }
        System.out.printf("There are %d numbers\n", calc.getCount());
        System.out.printf("Sum = %f\n", calc.getSum());
        System.out.printf("Mean = %f\n", calc.getMean());
        System.out.printf("Standard deviation = %f\n", calc.getStandardDeviation());
        System.out.printf("Max number = %f\n", calc.getMax());
        System.out.printf("Min number = %f\n", calc.getMin());
    }
}  // end class StatCalc
