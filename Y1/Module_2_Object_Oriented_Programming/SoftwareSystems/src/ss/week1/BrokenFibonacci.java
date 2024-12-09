package ss.week1;

import java.util.Scanner;

public class BrokenFibonacci {
    /**
     * Calculates the nth number in the fibonacci sequence
     * using arrays to store every number.
     * @param n the index of the nth number in the sequence
     * @return the nth fibonacci number
     */
    /**
     * Main function asks the user for a number and prints fibonacci(n)
     * @param args
     */

    public static void main(String[] args) {
        // Create a scanner and ask the user for how many fibo numbers to output
        Scanner sc = new Scanner(System.in);
        System.out.print("How many fibonacci numbers: ");
        int n = sc.nextInt();
        System.out.println(fibonacci(n));
    }

    public static long fibonacci(int n) {
        if (n < 2) {
            return n;
        } else {
            long[] array = new long[n + 1];
            array[0] = 1;
            array[1] = 1;
            for (int i = 2; i < n; i++) {
                array[i] = array[i - 1] + array[i - 2];
            }
            return array[n - 1];
        }
    }
}
