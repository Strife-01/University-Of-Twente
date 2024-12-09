package typeAnnotatorTestData;

public class JavaBooleanExpressions {
    boolean bool = false;

    //@ invariant getZero() == 0 && 8 > 7;
    //@ invariant true && false || bool ^ false | true & bool;
    // only show error on first problem
    //@ invariant true<error descr="This operator cannot be applied to type boolean and type Object"> && </error>new Object() || new Object() ^ false | new Object() & false;
    //@ invariant true && false || new Object()<error descr="This operator cannot be applied to type Object and type boolean"> ^ </error>false | new Object() & false;
    //@ invariant true && false || true ^ false | new Object()<error descr="This operator cannot be applied to type Object and type boolean"> & </error>false;
    // non existent variables, again, only show first problem
    //@ invariant true && false || <error descr="Reference cannot be resolved">z</error> ^ false | true & z;

    // conditional expressions
    //@ invariant true ? false : true;
    //@ invariant 10<error descr="This operator cannot be applied to type int and type boolean"> > </error>bool ? 5 : 9;
    //@ invariant 10 > (bool ? 5 : 9);
    //@ invariant <error descr="This must be of type boolean, but is int">10</error> ? true : false;
    //@ invariant <error descr="This must be of type boolean, but is int">getZero()</error> ? true : false;

    /*@pure*/int getZero() {
        return 0;
    }
}
