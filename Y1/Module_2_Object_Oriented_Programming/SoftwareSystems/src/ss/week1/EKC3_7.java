package ss.week1;

import java.lang.Math;

public class EKC3_7 {
    public static void main(String[] args) {
        System.out.printf("You needed to check %d many people to find 3 with the same birth day.\n", getAnswerPb1());
        System.out.printf("If we check 365 people we will find %d different birthdays.\n", getAnswerPb2());
        System.out.printf("You needed to check %d many people to find at least 1 person with a birthday for each day.\n", getAnswerPb3());

    }

    // Problem 1 how many people you have to randomly select before you find 3 with the same bday
    public static int getAnswerPb1() {
        int[] freq = new int[365];
        int count = 0;
        while (true) {
            count++;
            int bday = (int) (Math.random() * 365);
            freq[bday]++;
            if (freq[bday] == 3) {
                return count;
            }
        }
    }

    // Problem 2 if we choose 365 people at random, how many diff bdays will they have
    public static int getAnswerPb2() {
        int[] freq = new int[365];
        int count = 0;
        for (int i = 0; i < 365; i++) {
            int bday = (int) (Math.random() * 365);
            freq[bday]++;
        }
        for (int i = 0; i < 365; i++) {
            if (freq[i] > 0) {
                count++;
            }
        }
        return count;
    }

    // Problem 3 How many people we have to check until we find at least someone with bday in each 365 days
    public static int getAnswerPb3() {
        int[] freq = new int[365];
        int count = 0;
        while (true) {
            for (int i = 0; i < 365; i++) {
                if (freq[i] == 0) {
                    int bday = (int) (Math.random() * 365);
                    freq[bday]++;
                    i = 0;
                    count++;
                }
            }
            return count;
        }
    }
}
