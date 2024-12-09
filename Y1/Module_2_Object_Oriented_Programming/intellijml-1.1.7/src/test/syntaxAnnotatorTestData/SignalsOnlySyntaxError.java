package syntaxAnnotatorTestData;

public class SignalsOnlySyntaxError {

    //@signals_only<error descr="Reference(s) to one or more exceptions expected, got ';'">;</error>
    public int div(int a, int b) throws ArithmeticException {
        return a / b;
    }

    //@<error descr="Reference(s) to one or more exceptions expected after this token">signals_only</error>
    public int div2(int a, int b) throws ArithmeticException {
        return a / b;
    }

    //@signals_only ArithmeticException<error descr="Reference(s) to one or more exceptions expected after this token">,</error>
    public int div3(int a, int b) throws ArithmeticException {
        return a / b;
    }
}
