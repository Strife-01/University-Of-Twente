package semanticsAnnotatorTestData;

public class DuplicateModifiers {
    //@ nullable
    private int x; //@ <warning descr="This modifier has already been used in this specification">nullable</warning>

    /*@
        <warning descr="This modifier has already been used in this specification">pure</warning>;
        helper;
        <warning descr="This modifier has already been used in this specification">pure</warning>;
    */
    public int div(int a, int b) {
        return a / b;
    }

    //@ pure;
    //@ helper;
    //@ <warning descr="This modifier has already been used in this specification">pure</warning>;
    //@ <warning descr="This modifier has already been used in this specification">pure</warning>;
    public int div2(int a, int b) {
        return a / b;
    }

    /*@
        requires b != 0;
        pure;
    */
    //@ <warning descr="This modifier has already been used in this specification">pure</warning>;
    public int div3(int a, int b) {
        return a / b;
    }
}
