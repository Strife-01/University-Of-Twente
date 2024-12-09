package semanticsAnnotatorTestData;

public class HelperModifierAllowed {
    /*@
        @helper
        @pure
    */
    public int div(int a, int b) {
        return a / b;
    }

    //@pure;
    //@helper;
    public int div2(int a, int b) {
        return a / b;
    }

    /*@
        @helper
    */
    private int div3(int a, int b) {
        return a / b;
    }

    //@helper;
    private static int div4(int a, int b) {
        return a / b;
    }

    //@<error descr="The helper modifier is only allowed when the method is private or pure">helper</error>;
    public int div5(int a, int b) {
        return a / b;
    }

    //@<error descr="The helper modifier is only allowed when the method is private or pure">helper</error>;
    int div6(int a, int b) {
        return a / b;
    }
}
