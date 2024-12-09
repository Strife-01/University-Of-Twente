package completionTestData;

public class StaticDotSemicolon {

    /*@
    requires Integer.<caret>;
    */
    public int getInt(int methodParameter) {
        return methodParameter;
    }
}
