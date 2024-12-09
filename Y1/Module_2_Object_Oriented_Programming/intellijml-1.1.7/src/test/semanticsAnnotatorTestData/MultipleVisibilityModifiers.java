package semanticsAnnotatorTestData;

public class MultipleVisibilityModifiers {
    private int x = 5;

    //@ private <error descr="You cannot have multiple visibility modifiers (public, protected or private)">public</error> <error descr="You cannot have multiple visibility modifiers (public, protected or private)">protected</error> invariant x >= 5;
    /*@
    private
    <error descr="You cannot have multiple visibility modifiers (public, protected or private)">public</error>
    invariant x >= 5;
     */
}
