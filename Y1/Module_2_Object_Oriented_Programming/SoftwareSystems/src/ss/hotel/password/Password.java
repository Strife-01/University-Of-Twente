package ss.hotel.password;

/**
 * Representation of a password.
 */
public class Password {
    /**
     * The standard initial password.
     */
    private String password;
    private Checker checker;
    private String initPass;

    /*@
        private invariant checker != null;
        private invariant password.length() >= 6;
        private invariant (\forall int i; i < password.length(); password.charAt(i) != ' ');
        private invariant initPass.length() >= 6;
        private invariant (\forall int i; i < initPass.length(); initPass.charAt(i) != ' ');
    */

    /**
     * The constructor receives a checker and assigns it as the checker for this password.
     * The constructor uses the new checker to create an appropriate password based on the
     * checker's characteristics, and then it assigns it to the object in question.
     * @param checker the checker that creates the password
     */
    /*@
        requires checker != null;
        requires checker instanceof Checker;
        ensures checker.acceptable(initPass) == true ==> password == initPass;
        ensures checker.acceptable(password) == true;
    */
    public Password(Checker checker) {
        this.checker = checker;
        this.initPass = checker.generatePassword();
        this.password = this.initPass;
    }

    /**
     * The constructor calls the first constructor by assigning as a parameter a new BasicChecker.
     */
    /*@
        ensures checker != null;
        ensures checker instanceof BasicChecker;
        ensures checker.acceptable(initPass) == true ==> password == initPass;
        ensures checker.acceptable(password) == true;
    */
    public Password() {
        this(new BasicChecker());
    }

    /**
     * Test if a given string is an acceptable password.
     * Not acceptable: Not conformant with the checker's requirements.
     * @param suggestion Word that should be tested
     * @return true If suggestion is acceptable
     */
    /*@
        requires checker.acceptable(suggestion) == true;
        ensures checker.acceptable(suggestion) == true ==> \result == true;
        pure
    */
    public boolean acceptable(String suggestion) {
        return checker.acceptable(suggestion);
    }

    /**
     * Tests if a given word is equal to the current password.
     * @param passwordInQuestion Word that should be tested
     * @return true If test is equal to the current password
     */
    /*@
        requires passwordInQuestion.equals(this.password);
        ensures passwordInQuestion.equals(this.password) ==> \result == true;
        pure
    */
    public boolean testWord(String passwordInQuestion) {
        return this.password.equals(passwordInQuestion);
    }

    /**
     * Changes this password.
     * @param oldpass The current password
     * @param newpass The new password
     * @return true If oldPass is equal to the current password and newpass is an acceptable password
     */
    /*@
        requires oldpass.equals(this.password) && checker.acceptable(newpass);
        ensures oldpass.equals(this.password) && checker.acceptable(newpass) ==> \result == true
        && this.password == newpass;
    */
    public boolean setWord(String oldpass, String newpass) {
        if (oldpass.equals(this.password) && checker.acceptable(newpass)) {
            this.password = newpass;
            return true;
        }
        return false;
    }

    /**
     * Exposes the initial password.
     * @return initial password
     */
    /*@
        requires this.checker.acceptable(this.initPass) == true;
        ensures \result == this.initPass;
        pure
    */
    public String getInitPass() {
        return this.initPass;
    }

    /**
     * Exposes the checker.
     * @return the checker
     */
    /*@
        ensures \result == this.checker;
        pure
    */
    public Checker getChecker() {
        return this.checker;
    }
}
