package semanticsAnnotatorTestData;

public class MultipleSignalsOnly {
    /*@
        <warning descr="Use a single signals_only clause to avoid confusion">signals_only java.lang.Exception;</warning>
        <warning descr="Use a single signals_only clause to avoid confusion">signals_only ArithmeticException;</warning>
     */
    public int div(int a, int b) throws ArithmeticException {
        return a / b;
    }

    //@signals_only java.lang.Exception;
    //@<warning descr="Use a single signals_only clause to avoid confusion">signals_only ArithmeticException;</warning>
    public int div2(int a, int b) throws ArithmeticException {
        return a / b;
    }
}
