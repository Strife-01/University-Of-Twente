package completionTestData;

public class Signals {

    /*@
        signals(<caret>)
    */
    public int getException(int number) throws IllegalStateException {
        if (number == 0) {
            throw new IllegalStateException();
        } else {
            return number + 1;
        }
    }

}
