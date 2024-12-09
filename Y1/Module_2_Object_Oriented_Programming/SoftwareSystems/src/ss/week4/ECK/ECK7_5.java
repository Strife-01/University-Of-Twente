package ss.week4.ECK;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import ss.week4.MergeSort;

public class ECK7_5 {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        String input = "";
        List<Double> doubleList = new ArrayList<>();
        System.out.print("Number (0 to exit) = ");
        while (scanner.hasNextLine()) {
            input = scanner.nextLine();
            try {
                double num = Double.parseDouble(input);
                if (num == 0) {
                    break;
                }
                doubleList.add(num);
            } catch (NumberFormatException e) {
                System.out.println("Enter a valid number...");
                System.out.print("Number (0 to exit) = ");
                continue;
            }
            if (input.equals("0")) {
                break;
            }
            System.out.print("Number (0 to exit) = ");
        }

        doubleList = MergeSort.mergeSort(doubleList);
        System.out.println("Sorted list:");
        for (Double d : doubleList) {
            System.out.print(d + "  ");
        }
    }
}
