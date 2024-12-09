package ss.hotel.password;

public interface Checker {
    /**
     * Test if a given string is an acceptable password.
     * @param suggestion Word that should be tested
     * @return true If suggestion is acceptable
     */
    /*@
        requires suggestion.length() >= 6;
        requires suggestion.split("\\s+").length == 1;
        ensures suggestion.length() >= 6 && suggestion.split("\\s+").length == 1 ==>
        \result == true;
        pure
    */
    public boolean acceptable(String suggestion);

    /**
     * Generates an acceptable password based on requirements.
     * @return acceptable password
     */
    /*@
        ensures acceptable(\result) == true;
        pure
    */
    public String generatePassword();
}
