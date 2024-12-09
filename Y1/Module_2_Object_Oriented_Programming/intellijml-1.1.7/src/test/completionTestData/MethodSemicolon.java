package completionTestData;

public class MethodSemicolon {
    /*@
    requires <caret>;
    */
    public int getInt(int methodParameter) {
        return methodParameter;
    }

    public int randomNumber() {
        return 5;
    }
}
