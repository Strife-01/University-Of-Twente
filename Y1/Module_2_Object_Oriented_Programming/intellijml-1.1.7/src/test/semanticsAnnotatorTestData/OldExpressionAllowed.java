package semanticsAnnotatorTestData;

public class OldExpressionAllowed {
    //@ invariant <error descr="You can only use an \old() expressions in ensures and signals clauses, assert and assume statements, and in loop invariants">\old(1 > 0)</error>;

    //@ requires <error descr="You can only use an \old() expressions in ensures and signals clauses, assert and assume statements, and in loop invariants">\old(a > 0)</error>;
    //@ ensures \old(a > 0);
    //@ signals (Exception e) \old(a > 0);
    public int div(int a, int b) {
        //@ assert \old(a > 0);
        //@ assume \old(a > 0);

        boolean loop = true;
        //@ maintaining \old(a > 0);
        //@ loop_invariant \old(a > 0);
        while (loop) {
            System.out.println("Hello world");
            loop = false;
        }
        return a / b;
    }
}
