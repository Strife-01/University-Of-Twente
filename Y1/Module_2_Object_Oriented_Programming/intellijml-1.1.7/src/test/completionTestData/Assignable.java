package completionTestData;

public class Assignable {

    public int number = 5;

    /*@
        requires true;
        ensures true;
        assignable <caret>
    */
    public int getRandomNumber() {
        return 0;
    }
}
