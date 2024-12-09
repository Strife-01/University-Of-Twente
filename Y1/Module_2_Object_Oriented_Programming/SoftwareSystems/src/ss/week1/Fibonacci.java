package ss.week1;

import java.util.Scanner;

public class Fibonacci {
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

    /**
     * The function reccursively checks for a fibonacci number
     * @param n - nth fibonacci number
     * @return fibonacci number
     */
    public static int fibonacci(int n) {
        if (n < 2) {
            return n;
        }
        return fibonacci(n - 1) + fibonacci(n - 2);
    }
}
