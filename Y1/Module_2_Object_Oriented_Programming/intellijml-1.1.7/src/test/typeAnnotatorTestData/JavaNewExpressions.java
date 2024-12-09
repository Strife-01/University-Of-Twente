package typeAnnotatorTestData;

public class JavaNewExpressions {
    int x;

    public JavaNewExpressions(int i) {
    }

    public JavaNewExpressions(boolean b) {
    }

    // creating a new array
    //@ invariant (new int[1])[0] > 0;
    //@ invariant (new int[]{1,2})[0] > 0;
    //@ invariant (new int[]{})[0] > 0;
    //@ invariant (new int[]<error descr="Array initializer expected"></error>)[0] > 0;
    //@ invariant (new int['a'])[0] > 0;
    //@ invariant (new int[<error descr="Array dimensions should be of type int or something that can be converted to int">"str"</error>])[0] > 0;
    //@ invariant (new int[<error descr="Array dimensions should be of type int or something that can be converted to int">new Object()</error>])[0] > 0;
    //@ invariant (new int[Integer.valueOf(5)])[0] > 0;

    // creating a new object
    //@ invariant new Object() == null;
    //@ invariant <error descr="Constructor could not be resolved, maybe the parameters do not correspond?">new JavaNewExpressions()</error> == null;
    //@ invariant new JavaNewExpressions(8) == null;
    //@ invariant new JavaNewExpressions(true) == null;
    //@ invariant <error descr="Constructor could not be resolved, maybe the parameters do not correspond?">new JavaNewExpressions("string")</error> == null;
    //@ invariant new <error descr="Reference cannot be resolved">NonExistent</error>() == null;
    // cannot be resolved as the resolver is looking for a class
    //@ invariant new <error descr="Reference cannot be resolved">test</error>() == null;
    //@ invariant new <error descr="Reference cannot be resolved">x</error>() == null;

    // implicit constructor
    //@ invariant new JavaNewExpressions2() == null;

    void test() {

    }
}

class JavaNewExpressions2 {

}
