package ss.week4.ECK;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Random;

public class ECK7_3 {
    public static void selectionSort(int[] arr) {
        int n = arr.length;
        for (int i = 0; i < n - 1; i++) {
            int minIndex = i;
            // Find the smallest element in the remaining unsorted part
            for (int j = i + 1; j < n; j++) {
                if (arr[j] < arr[minIndex]) {
                    minIndex = j;
                }
            }
            // Swap the found minimum with the first element of the unsorted part
            int temp = arr[minIndex];
            arr[minIndex] = arr[i];
            arr[i] = temp;
        }
    }

    public static void main(String[] args) {
        int cap = 100000;
        long startTime, endTime;
        Random random = new Random();
        int[] arr1 = new int[cap];
        int[] arr2 = new int[cap];

        for (int i = 0; i < cap; i++) {
            arr1[i] = random.nextInt(cap);
            arr2[i] = random.nextInt(cap);
        }

        System.out.println("Starting sorting competition now!");

        startTime = System.nanoTime();
        Arrays.sort(arr1);
        endTime = System.nanoTime();
        System.out.printf("Array.sort() took %f second\n", (endTime - startTime) / 1000000000.0);
        startTime = System.nanoTime();
        selectionSort(arr2);
        endTime = System.nanoTime();
        System.out.printf("selectionSort() took %f\n", (endTime - startTime) / 1000000000.0);
    }
}
