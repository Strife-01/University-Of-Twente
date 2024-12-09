package syntaxAnnotatorTestData;

public class QuantifierSyntax {
    //@ ensures (\forall int i; i > 0 && i < 10; i+5 >= 5);
    //@ ensures <error descr="A quantified expression should be inside parentheses, including the keyword">\forall</error> (int i; i > 0 && i < 10; i+5 >= 5);
    //@ ensures <error descr="A quantified expression should be inside parentheses, including the keyword">\forall</error> int i; i > 0 && i < 10; i+5 >= 5
    //@ ensures <error descr="A quantified expression should be inside parentheses, including the keyword">\forall</error>
    //@ ensures (<error descr="Variable declaration expected after this token">\forall</error>
    //@ ensures (\forall <error descr="Identifier or left bracket expected after this token">int</error>
    //@ ensures (\forall int <error descr="Comma, left bracket or semicolon expected after this token">i</error>
    //@ ensures (\forall int i<error descr="Range condition or expression expected after this token">;</error>
    //@ ensures (\forall int i; i > 0 && i < <error descr="Right parenthesis or semicolon expected after this token">10</error>
    //@ ensures (\forall int i; i > 0 && i < 10; i+5 >= <error descr="Right parenthesis expected after this token">5</error>
    //@ ensures (\forall int i;; i+5 >= 5);
    //@ ensures (\forall int i; i > 0 && i < 10;<error descr="Expression expected, got ')'">)</error>;
    //@ ensures (\forall int i; i > 0 && i < 10);
    //@ ensures (\forall int i;<error descr="Range condition or expression expected, got ')'">)</error>;
    //@ ensures (\forall int i<error descr="Comma, left bracket or semicolon expected, got ')'">)</error>;
    public void loop(int[] arr) {

    }
}
