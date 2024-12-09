package semanticsAnnotatorTestData;

public class BackslashResultAllowed {

    //@ invariant <error descr="You can only use \result in an ensures clause">\result</error> == null;

    /*@
        requires <error descr="You can only use \result in an ensures clause">\result</error> == 0;
        ensures \result > 10;
        signals(Exception e) <error descr="You can only use \result in an ensures clause">\result</error> == 0;
    */
    public int div(int a, int b) {
        return a / b;
    }
}
