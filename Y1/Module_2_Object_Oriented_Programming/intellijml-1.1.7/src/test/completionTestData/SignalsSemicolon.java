package completionTestData;

public class SignalsSemicolon {

    /*@
        signals(<caret>);
    */
    public int getException(int number) throws IllegalStateException {
        if (number == 0) {
            throw new IllegalStateException();
        } else {
            return number + 1;
        }
    }

}
