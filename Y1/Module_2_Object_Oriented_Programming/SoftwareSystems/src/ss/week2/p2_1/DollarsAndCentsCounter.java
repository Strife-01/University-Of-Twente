package ss.week2.p2_1;

public class DollarsAndCentsCounter {
    private int dollars;
    private int cents;
    /*@
       private invariant dollars >= 0;
       private invariant cents >= 0;
    */

    /**
     * Implicit constructor.
     * In case of no arguments set both fields to 0.
     */
    /*@
        ensures this.dollars == 0;
        ensures this.dollars == 0;
    */
    public DollarsAndCentsCounter() {
        this.dollars = 0;
        this.cents = 0;
    }

    /**
     * Takes 1 argument meaning only the dollars from user.
     * @param dollars provided amount of dollars
     */

    /*@
        requires dollars >= 0;
        ensures this.dollars >= 0;
    */
    public DollarsAndCentsCounter(int dollars) {
        if (dollars < 0) {
            throw new RuntimeException("Dollars cannot be zero");
        }
        this.dollars = dollars;
    }

    /**
     * Takes the 2 amounts from user representing dollars and cents and correctly assigns them.
     * @param dollars provided amount of dollars
     * @param cents provided amount of cents
     */
    /*@
        requires dollars >= 0;
        requires cents >= 0;
        ensures this.dollars >= 0;
        ensures this.dollars >= 0;
    */
    public DollarsAndCentsCounter(int dollars, int cents) {
        if (dollars < 0 || cents < 0) {
            throw new RuntimeException("Dollars or cents cannot be less than zero.");
        }
        this.dollars = dollars + cents / 100;
        this.cents = cents % 100;
    }

    /**
     * Gets the value in the dollars field.
     * @return an integer representing dollars
     */

    /*@
        ensures (\result == this.dollars);
        pure
    */
    public int getDollars() {
        return this.dollars;
    }

    /**
     * Gets the value under the cents field.
     * @return an integer representing cents
     */

    /*@
        ensures (\result == this.cents);
        pure;
    */
    public int getCents() {
        return this.cents;
    }

    /**
     * Mutates the fileds dollars and cents with the appropriate values.
     * @param dollars amount representing dollars
     * @param cents amount representing cents
     */
    /*@
        requires (this.dollars * 100 + this.cents) - (dollars * 100 + cents) >= 0;
        ensures this.dollars >= 0;
        ensures this.cents >= 0;
    */
    public void add(int dollars, int cents) {
        int validator = this.dollars * 100 + this.cents + dollars * 100 + cents;
        if (validator < 0) {
            throw new RuntimeException("Balance cannot be negative");
        }
        this.dollars = validator / 100;
        this.cents = validator % 100;
    }

    /**
     * Resets the filed variables.
     */
    /*@
        ensures this.dollars == 0;
        ensures this.cents == 0;
    */
    public void reset() {
        this.dollars = 0;
        this.cents = 0;
    }

    // Main function
    public static void main(String[] args) {
    }
}
