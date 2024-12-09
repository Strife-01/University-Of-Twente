package completionTestData;

public class ModifiesSemicolon {

    public int number = 5;

    /*@
        requires true;
        ensures true;
        modifies <caret>;
    */
    public int getRandomNumber() {
        return 0;
    }
}
