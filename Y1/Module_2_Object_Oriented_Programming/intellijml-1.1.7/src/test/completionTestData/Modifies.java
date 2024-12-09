package completionTestData;

public class Modifies {

    public int number = 5;

    /*@
        requires true;
        ensures true;
        modifies <caret>
    */
    public int getRandomNumber() {
        return 0;
    }
}
