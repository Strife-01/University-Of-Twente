package semanticsAnnotatorTestData;

public class ModifierBeforeClause {

    //@ pure;
    //@ <error descr="All specification cases must be placed before any modifiers">requires b!=0;</error>
    //@ <error descr="All specification cases must be placed before any modifiers">ensures \result ==a/b;</error>
    public int div(int a, int b) {
        return a / b;
    }
}
