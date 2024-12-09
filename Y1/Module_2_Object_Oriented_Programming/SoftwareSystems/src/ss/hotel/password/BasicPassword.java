package ss.hotel.password;

import java.lang.Math;

import java.lang.Character;

/**
 * Representation of a password.
 */
public class BasicPassword {
    /**
     * The standard initial password.
     */
    public static final String INITIAL = "123456";
    private String password;
    public int minLength = 6;

    /*@
        public invariant minLength >= 6;
        private invariant password.length() >= 6;
        private invariant (\forall int i; i < password.length(); password.charAt(i) != ' ');
        public invariant INITIAL.length() >= this.minLength;
        public invariant (\forall int i; i < INITIAL.length(); INITIAL.charAt(i) != ' ');
    */

    /**
     * Constructs a Password with the initial word provided in INITIAL.
     */
    /*@
        requires INITIAL != null;
        requires acceptable(INITIAL) == true;
        ensures acceptable(INITIAL) == true ==> password == INITIAL;
        ensures acceptable(password) ==true;
    */
    public BasicPassword() {
        this.password = INITIAL;
    }

    /**
     * Test if a given string is an acceptable password.
     * Not acceptable: A word with less than 6 characters
     * or a word that contains a space.
     * @param suggestion Word that should be tested
     * @return true If suggestion is acceptable
     */
    /*@
        requires suggestion.length() >= this.minLength;
        requires (\forall int i; i < suggestion.length(); suggestion.charAt(i) != ' ');
        ensures suggestion.length() >= this.minLength &&
        (\forall int i; i < suggestion.length(); suggestion.charAt(i) != ' ') ==> \result == true;
        pure
    */
    public boolean acceptable(String suggestion) {
        return suggestion.length() >= this.minLength && suggestion.split("\\s+").length == 1;
    }

    /**
     * Tests if a given word is equal to the current password.
     * @param test Word that should be tested
     * @return true If test is equal to the current password
     */
    /*@
        requires test.equals(this.password);
        ensures test.equals(this.password) ==> \result == true;
        pure
    */
    public boolean testWord(String test) {
        return this.password.equals(test);
    }

    /**
     * Changes this password.
     * @param oldpass The current password
     * @param newpass The new password
     * @return true If oldPass is equal to the current password and newpass is an acceptable password
     */
    /*@
        requires oldpass.equals(this.password) && acceptable(newpass);
        ensures oldpass.equals(this.password) && acceptable(newpass) ==> \result == true
        && this.password == newpass;
    */
    public boolean setWord(String oldpass, String newpass) {
        if (oldpass.equals(this.password) && acceptable(newpass)) {
            this.password = newpass;
            return true;
        }
        return false;
    }
}
