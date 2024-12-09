package typeAnnotatorTestData;

public class JavaArrays {
    int[] arr = new int[5];
    int notArr = 5;

    // tests that array accessor is int
    //@ invariant arr[0] > 0;
    //@ invariant arr['c'] > 0;
    //@ invariant arr[<error descr="This must be of type int or something that can be converted to int, but is boolean">true</error>] > 0;
    //@ invariant arr[10] > 0;
    //@ invariant arr[8+9+1] > 0;
    //@ invariant arr[Integer.valueOf(5)] > 0;
    //@ invariant arr[<error descr="This must be of type int or something that can be converted to int, but is String">"test"</error>] > 0;
    //@ invariant arr[<error descr="This must be of type int or something that can be converted to int, but is Object">new Object()</error>] > 0;

    // tests that it is actually trying to access an array
    //@ invariant <error descr="Array access is not allowed as this is not an array">notArr</error>[0] > 0;
    //@ invariant <error descr="Array access is not allowed as this is not an array">new Object()</error>[0] > 0;

    // no accessor
    //@ invariant <error descr="Not a valid expression">arr[] > 0</error>;

    // test arrays in \result
    //@ ensures \result[0] == 5;
    //@ ensures \result<error descr="This operator cannot be applied to type int[] and type int"> == </error>5;
    //@ ensures <error descr="Array access is not allowed as this is not an array">\result[0]</error>[0] == 5;
    public int[] getArr() {
        return new int[10];
    }

    //@ ensures \result[0]<error descr="This operator cannot be applied to type int[][] and type int"> == </error>5;
    //@ ensures \result[0]<error descr="This operator cannot be applied to type int[][] and type int[]"> == </error>new int[7];
    //@ ensures \result[0][1]<error descr="This operator cannot be applied to type int[] and type int"> == </error>5;
    //@ ensures \result[0][1] == new int[7];
    //@ ensures \result[0][1][2] == 5;
    public int[][][] getArr2() {
        return new int[10][10][10];
    }
}
