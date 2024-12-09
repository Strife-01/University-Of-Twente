package ss.week1;

import java.util.Arrays;
import java.util.Scanner;

public class ParseInts {
    public static void main(String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("Please enter some numbers: ");
        String s = sc.nextLine();
        String[] numbers = s.trim().split("\\s+");
        int[] nums = new int[numbers.length];
        for (int i = 0; i < numbers.length; i++) {
            nums[i] = Integer.parseInt(numbers[i]);
        }
        Arrays.sort(nums);
        for (int i = 0; i < nums.length; i++) {
            System.out.print(nums[i] + " ");
        }
        //System.out.println(Arrays.toString(nums));
    }
}
