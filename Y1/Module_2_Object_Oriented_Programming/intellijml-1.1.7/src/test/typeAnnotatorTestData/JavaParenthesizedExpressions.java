package typeAnnotatorTestData;

public class JavaParenthesizedExpressions {
    int test;

    //@invariant (((((8 > 7)))));
    //@invariant (((test>8) && ((test > 7))));
    //@invariant <error descr="Not a valid expression">() (8 >7)</error>;
}
