package ss.week1;

public class ECK3_2 {
    public static void main(String[] args) {
        final int MAXIMUM_NUMBER = 10000;
        // frequency array
        int[] frequency = new int[MAXIMUM_NUMBER + 1];

        for (int i = 1; i <= MAXIMUM_NUMBER; i++) {
            frequency[i] = getNrDivisors(i);
        }

        System.out.println("Number with most divisors between 1 and "
                                   + MAXIMUM_NUMBER
                                   + " is "
                                   + getNrWithMostDivisors(MAXIMUM_NUMBER, frequency)
                                   + " and it has "
                                   + frequency[getNrWithMostDivisors(MAXIMUM_NUMBER, frequency)]
                                   + " divisors."
        );
    }

    public static int getNrDivisors(int number) {
        int count = 0;
        for (int i = 1; i <= number / 2; i++) {
            if (number % i == 0) {
                count++;
            }
        }
        return count;
    }

    public static int getNrWithMostDivisors(int number, int[] frequency) {
        int max = 1;
        for (int i = 1; i <= number; i++) {
            if (frequency[i] > frequency[max]) {
                max = i;
            }
        }
        return max;
    }
}
