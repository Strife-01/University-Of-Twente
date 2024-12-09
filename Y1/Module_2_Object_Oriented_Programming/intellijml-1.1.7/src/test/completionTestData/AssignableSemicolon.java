package completionTestData;

public class AssignableSemicolon {

    public int number = 5;

    /*@
        requires true;
        ensures true;
        assignable <caret>;
    */
    public int getRandomNumber() {
        return 0;
    }
}
