package completionTestData;

public class QuantifiedCondition {

    public int fieldInt = 0;

    /*@
        requires (\sum int x; <caret> ; )
    */
    public int getRandomNumber() {
        return 0;
    }
}
