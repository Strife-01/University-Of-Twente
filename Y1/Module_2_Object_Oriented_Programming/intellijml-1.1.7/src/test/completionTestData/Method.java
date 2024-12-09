package completionTestData;

public class Method {
    /*@
    requires <caret>
    */
    public int getInt(int methodParameter) {
        return methodParameter;
    }

    public int randomNumber() {
        return 5;
    }
}
