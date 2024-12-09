package syntaxAnnotatorTestData;

public class SignalsWithoutParens {

    /*@
        signals(ArithmeticException e) a == \old(a);
     */
    public int div(int a, int b) throws ArithmeticException {
        return a / b;
    }

    /*@
        signals <error descr="A signals clause must have parentheses around the exception type">ArithmeticException</error> e) a == \old(a);
     */
    public int div2(int a, int b) throws ArithmeticException {
        return a / b;
    }

    /*@
        signals(ArithmeticException e <error descr="A signals clause must have parentheses around the exception type">a</error> == \old(a);
     */
    public int div3(int a, int b) throws ArithmeticException {
        return a / b;
    }
}
