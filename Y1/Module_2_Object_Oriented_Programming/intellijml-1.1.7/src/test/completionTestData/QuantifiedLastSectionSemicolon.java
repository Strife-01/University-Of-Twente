package completionTestData;

public class QuantifiedLastSectionSemicolon {

    public int fieldInt = 5;

    /*@
        requires (\sum int x; x < 10 ; <caret>);
    */
    public int getSomeNumber() {
        return 0;
    }
}
