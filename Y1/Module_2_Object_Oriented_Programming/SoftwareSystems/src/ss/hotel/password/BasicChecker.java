package ss.hotel.password;

import java.util.Random;

public class BasicChecker implements Checker {
    protected static final int MIN_LENGTH = 6;
    protected static final int ASCII_START = 33; // Start of printable ASCII range ('!')
    protected static final int ASCII_END = 126;  // End of printable ASCII range ('~')
    private final Random random = new Random();

    /*@
        protected invariant MIN_LENGTH >= 6;
    */

    /**
     * Tests if a given string is an acceptable password.
     * A password is unacceptable if it:
     * - Has fewer than 6 characters.
     * - Contains any whitespace characters.
     *
     * @param suggestion Word to be tested.
     * @return true if the suggestion is acceptable, false otherwise.
     */
    /*@
        requires suggestion != null;
        ensures suggestion.length() >= MIN_LENGTH &&
                (\forall int i; 0 <= i && i < suggestion.length(); suggestion.charAt(i) != ' ') ==> \result == true;
        pure
    */
    public boolean acceptable(String suggestion) {
        if (suggestion == null || suggestion.length() < MIN_LENGTH) {
            return false;
        }
        for (char c : suggestion.toCharArray()) {
            if (Character.isWhitespace(c)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Generates an acceptable password that meets the minimum length requirement.
     *
     * @return an acceptable password.
     */
    /*@
        ensures \result.length() == MIN_LENGTH &&
                (\forall int i; 0 <= i && i < \result.length(); !Character.isWhitespace(\result.charAt(i)));
        pure
    */
    @Override
    public String generatePassword() {
        StringBuilder password = new StringBuilder(MIN_LENGTH);
        for (int i = 0; i < MIN_LENGTH; i++) {
            password.append(generateRandomAlphanumeric());
        }
        return password.toString();
    }

    /**
     * Generates a random alphanumeric character (letter or digit).
     *
     * @return a random alphanumeric character.
     */
    /*@
        ensures Character.isLetterOrDigit(\result);
        pure
    */
    public char generateRandomAlphanumeric() {
        char c;
        do {
            c = generateRandomPrintableCharacter();
        } while (!Character.isLetterOrDigit(c));
        return c;
    }

    /**
     * Generates a random printable ASCII character.
     *
     * @return a random printable ASCII character.
     */
    /*@
        ensures ASCII_START <= \result && \result <= ASCII_END;
        pure
    */
    public char generateRandomPrintableCharacter() {
        return (char) (ASCII_START + random.nextInt(ASCII_END - ASCII_START + 1));
    }

    public static void main(String[] args) {
        BasicChecker checker = new BasicChecker();
        System.out.println("Generated Password: " + checker.generatePassword());
    }
}
