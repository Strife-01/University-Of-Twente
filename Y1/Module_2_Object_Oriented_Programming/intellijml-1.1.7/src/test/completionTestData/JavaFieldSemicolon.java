package completionTestData;

public class JavaFieldSemicolon {

    public int number = 5;

    /*@
   requires <caret>;
    */
    public static int getInt() {
        return 2;
    }
}