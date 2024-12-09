package completionTestData;

public class StaticDot {

    /*@
    requires Integer.<caret>
    */
    public int getInt(int methodParameter) {
        return methodParameter;
    }
}
