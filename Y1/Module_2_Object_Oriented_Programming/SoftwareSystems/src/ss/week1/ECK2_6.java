package ss.week1;

import java.util.Locale;
import java.util.Scanner;

public class ECK2_6 {
    public static void main(String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.print("Please enter your first name and last name, separated by a space.\n" + "? ");
        String fullName = sc.nextLine();
        String[] names = fullName.trim().split(" ");
        String lastName = names[names.length - 1];
        String firstName = names[0];
        System.out.println("Your first name is "
                                   + firstName.substring(0, 1).toUpperCase()
                                   + firstName.substring(1).toLowerCase()
                                   + ", which has "
                                   + firstName.length()
                                   + " characters"
        );
        System.out.println("Your last name is "
                                   + lastName.substring(0, 1).toUpperCase()
                                   + lastName.substring(1).toLowerCase()
                                   + ", which has "
                                   + lastName.length()
                                   + " characters"
        );
        System.out.println("Your initials are "
                                   + firstName.substring(0, 1).toUpperCase()
                                   + lastName.substring(0, 1).toUpperCase()
        );
    }
}
