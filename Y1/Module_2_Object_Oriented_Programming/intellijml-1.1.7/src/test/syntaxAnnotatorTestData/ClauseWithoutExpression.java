package syntaxAnnotatorTestData;

public class ClauseWithoutExpression {
    //@ <error descr="Expression expected after this token">invariant</error>
    //@ invariant <error descr="Expression expected, got ';'">;</error>
    //@ invariant <error descr="Expression expected, got ';'">;</error>;;;;

    /*@
        <error descr="'\not_specified' or expression expected after this token">ensures</error>
    */
    /*@
        ensures
        <error descr="'\not_specified' or expression expected, got 'ensures'">ensures</error> \result == a / b;
        (* checks that it does not parse the second ensures as Java expression *)
    */
    public int div(int a, int b) {
        return a / b;
    }

    /*@
        ensures <error descr="'\not_specified' or expression expected, got ';'">;</error>
    */
    public int div2(int a, int b) {
        int i = 10;
        //@ <error descr="Expression expected after this token">maintaining</error>
        while (i > 0) {
            i--;
        }
        //@ <error descr="Expression expected after this token">assert</error>
        //@ <error descr="Expression expected after this token">assume</error>
        return a / b;
    }
}
