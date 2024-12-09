package syntaxAnnotatorTestData;

public class WhitespaceAroundAt {
    /*@
            requires b!=0;
    */
    public int div(int a, int b) {
        return a / b;
    }

    /* <weak_warning descr="To be considered a JML comment, there should be no whitespace between the start of the comment (/* or //) and the @-sign">@</weak_warning>
        requires b != 0;
     */
    public int div2(int a, int b) {
        return a / b;
    }
}