package completionTestData;

public class JavaField {

    public int number = 5;

    /*@
   requires <caret>
    */
    public static int getInt() {
        return 2;
    }
}
