package ss.hotel.password;

import java.util.Random;

public class StrongChecker extends BasicChecker {

    private final Random random = new Random();

    /**
     * Tests if a given string is an acceptable password.
     * A password is unacceptable if it:
     * - Has fewer than the minimum length.
     * - Contains any whitespace characters.
     * - Does not start with a letter.
     * - Does not end with a digit.
     *
     * @param suggestion Word to be tested.
     * @return true if the suggestion is acceptable, false otherwise.
     */
    @Override
    public boolean acceptable(String suggestion) {
        if (suggestion == null || suggestion.length() < MIN_LENGTH) {
            return false;
        }
        if (!Character.isLetter(suggestion.charAt(0)) || !Character.isDigit(suggestion.charAt(suggestion.length() - 1))) {
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
     * Generates an acceptable password that meets the strong password requirements:
     * - Starts with a letter.
     * - Ends with a digit.
     * - Contains any printable ASCII characters in the middle.
     *
     * @return an acceptable password.
     */
    @Override
    public String generatePassword() {
        StringBuilder password = new StringBuilder(MIN_LENGTH);

        // Start with a random letter
        password.append(generateRandomLetter());

        // Fill the middle characters with random printable characters
        for (int i = 1; i < MIN_LENGTH - 1; i++) {
            password.append(generateRandomPrintableCharacter());
        }

        // End with a random digit
        password.append(generateRandomDigit());

        return password.toString();
    }

    /**
     * Generates a random ASCII letter.
     *
     * @return a random letter (uppercase or lowercase).
     */
    public char generateRandomLetter() {
        return (char) (random.nextBoolean() ? 'A' + random.nextInt(26) : 'a' + random.nextInt(26));
    }

    /**
     * Generates a random ASCII digit.
     *
     * @return a random digit ('0' to '9').
     */
    public char generateRandomDigit() {
        return (char) ('0' + random.nextInt(10));
    }

    /**
     * Generates a random printable ASCII character.
     *
     * @return a random printable character.
     */
    public char generateRandomPrintableCharacter() {
        return (char) (ASCII_START + random.nextInt(ASCII_END - ASCII_START + 1));
    }

    public static void main(String[] args) {
        StrongChecker checker = new StrongChecker();
        System.out.println("Generated Password: " + checker.generatePassword());
    }
}
