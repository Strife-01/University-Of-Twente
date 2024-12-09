package completionTestData;

public class QuantifiedInitializationSemicolon {

    /*@
        requires (\sum <caret>; ; );
    */
    public int getSomethingRandom() {
        return 0;
    }
}
