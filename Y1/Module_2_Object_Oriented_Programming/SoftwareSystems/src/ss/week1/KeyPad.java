package ss.week1;

import java.util.Scanner;

public class KeyPad {
    /**
     * Asks the user for a string of characters and turns them into a keypad sequece
     * @param args
     */
    public static void main(String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.print("Please enter a word: ");
        String word = sc.nextLine();
        sc.close();
        char[] chars = word.toCharArray();
        String nrSequence = "";
        for (int i = 0; i < chars.length; i++) {
            nrSequence += switch (Character.toLowerCase(chars[i])) {
                case 'a', 'b', 'c' -> 2;
                case 'd', 'e', 'f' -> 3;
                case 'g', 'h', 'i' -> 4;
                case 'j', 'k', 'l' -> 5;
                case 'm', 'n', 'o' -> 6;
                case 'p', 'q', 'r', 's' -> 7;
                case 't', 'u', 'v' -> 8;
                case 'w', 'x', 'y', 'z' -> 9;
                default -> "";
            };
        }
        System.out.println(nrSequence);
    }
}
