package syntaxAnnotatorTestData;

public class MissingSemicolon {

    /*@
        requires b != <error descr="Semicolon expected after this token">0</error>
     */
    public int div(int a, int b) {
        return a / b;
    }

    /*@
        requires <error descr="Semicolon expected after this token">\not_specified</error>
     */
    public int div2(int a, int b) {
        return a / b;
    }
}
