package ss.week1;

import java.util.Scanner;

public class ECK3_4 {
    public static void main(String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.println("Please enter a line of text to be stripped and segmented per words:");
        String line = sc.nextLine();

        String[] words = line.split(" ");
        for (int j = 0; j < words.length; j++) {
            String word = words[j];
            String cleanWord = "";
            for (int i = 0; i < word.length(); i++) {
                if (Character.isLetter(word.charAt(i))) {
                    cleanWord += word.charAt(i);
                } else if (word.charAt(i) == '’' && Character.isLetter(word.charAt(i + 1))) {
                    cleanWord += word.charAt(i);
                    cleanWord += word.charAt(i + 1);
                    i++;
                }
            }
            words[j] = cleanWord;
        }

        for (String word : words) {
            System.out.println(word);
        }
    }
}
