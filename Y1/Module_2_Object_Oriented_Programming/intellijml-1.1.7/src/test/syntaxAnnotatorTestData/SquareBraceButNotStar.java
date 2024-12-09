package syntaxAnnotatorTestData;

public class SquareBraceButNotStar {
    int[] a;

    //@ assignable a[*];
    //@ assignable a [<error descr="Only '*' in between the square brackets is supported">x</error>];
    //@ assignable a[<error descr="Only '*' in between the square brackets is supported">0</error>..10];
    public void test(int x) {
        Object[] a;
    }
}
