package ss.week1;

import java.util.Scanner;

/**
 * This class will be used to calculate the first N prime numbers
 * N provided from the std input from user
 */
public class FirstNPrimes {
    /**
     * this is the main function which represents the entry point for the program
     * @param args
     */
    public static void main(String[] args) {
        // Prepare a scanner
        Scanner sc = new Scanner(System.in);
        // Prompt user for how many primes they want printed
        System.out.print("How many primes ? ");
        int N = sc.nextInt();
        // Search for primes 1 number at a time
        int currentNumber = 2;
        int incrementer = 0;
        while (incrementer < N) {
            if (isPrime(currentNumber)) {
                System.out.print(currentNumber + " ");
                incrementer++;
            }
            currentNumber++;
        }
    }

    /**
     * This boolean function checks whether or not a provided number as argument is prime or not
     * @param n - number we want to check if is prime
     * @return true if number is prime else false
     */
    public static boolean isPrime(int n) {
        // Efficiently check for divisors
        for (int i = 2; i * i <= n; i++) {
            if (n % i == 0) {
                return false;
            }
        }
        return true;
    }
}
