package ss.week4.ECK;

import java.util.Random;

public class ECK7_2 {
    public static int[][] transpose(int[][] array) {
        int[][] transpose = new int[array[0].length][array.length];
        for (int i = 0; i < array.length; i++) {
            for (int j = 0; j < array[i].length; j++) {
                transpose[j][i] = array[i][j];
            }
        }
        return transpose;
    }
    public static void main(String[] args) {
        int [][] arr = new int[3][5];
        Random random = new Random();
        for (int i = 0; i < arr.length; i++) {
            for (int j = 0; j < arr[i].length; j++) {
                arr[i][j] = random.nextInt(30);
            }
        }
        for (int i = 0; i < arr.length; i++) {
            for (int j = 0; j < arr[i].length; j++) {
                System.out.print(arr[i][j] + " ");
            }
            System.out.println();
        }
        System.out.println();
        System.out.println();
        int[][] tArr = transpose(arr);
        for (int i = 0; i < tArr.length; i++) {
            for (int j = 0; j < tArr[i].length; j++) {
                System.out.print(tArr[i][j] + " ");
            }
            System.out.println();
        }
    }
}
