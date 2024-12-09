package ss.week1;

import java.util.Scanner;

public class Emirps {
    public static void main(String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.print("How many emirps ? ");
        int n = sc.nextInt();
        int currentNumber = 1;
        while (n > 0) {
            if (isPrime(currentNumber) && isEmirp(currentNumber)) {
                System.out.print(currentNumber + " ");
                --n;
            }
            ++currentNumber;
        }
    }

    /**
     * The function tests if the provided number is a prime number.
     * @param number what we are testing for prime
     * @return true if prime false otherwise
     */
    public static boolean isPrime(int number) {
        for (int i = 2; i * i <= number; i++) {
            if (number % i == 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * It takes an int as an argument, and it returns the reversed number.
     * @param number number to be reversed
     * @return reversed number
     */
    public static int reverse(int number) {
        int newNumber = 0;
        while (number != 0) {
            int temp = number % 10;
            number /= 10;
            newNumber = newNumber * 10 + temp;
        }
        return newNumber;
    }

    /**
     * we take a number as argument, and first we reverse it and then check if it is prime.
     * @param number the number we want to check if it is emirp
     * @return true if emirp else false
     */
    public static boolean isEmirp(int number) {
        int n = reverse(number);
        return (number != n) && isPrime(n);
    }
}
