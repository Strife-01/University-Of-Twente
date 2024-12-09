package completionTestData;

public class Modifiable {

    public int number = 5;

    /*@
        requires true;
        ensures true;
        modifiable <caret>
    */
    public int getRandomNumber() {
        return 0;
    }
}
