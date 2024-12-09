package typeAnnotatorTestData;

public class JavaInstanceofAndCasting {
    Test variable = new Test();

    //@ invariant ((Test) variable).getZero() == 0;
    //@ invariant (<warning descr="Test is a subtype of JavaInstanceofAndCasting, so this might produce a ClassCastException">(Test) new JavaInstanceofAndCasting()</warning>).getZero() == 0;
    //@ invariant ((JavaInstanceofAndCasting) new JavaInstanceofAndCasting()).getZero() == 0;
    //@ invariant ((JavaInstanceofAndCasting) variable).getZero() == 0;
    // == 0 does not get error as there is already an error before it
    //@ invariant (<error descr="Expression of type JavaInstanceofAndCasting cannot be cast to Test2">(Test2) new JavaInstanceofAndCasting()</error>) == 0;
    //@ invariant (<error descr="Expression of type Test cannot be cast to Test2">(Test2) variable</error>) == 0;
    //@ invariant ((Test) new Object()).getZero() == 0;
    //@ invariant (<error descr="Expression of type Test2 cannot be cast to Test">(Test) new Test2()</error>).getZero() == 0;

    //@ invariant variable instanceof Test;
    //@ invariant variable instanceof JavaInstanceofAndCasting;
    //@ invariant variable instanceof Object;
    //@ invariant <error descr="Expression of type Test can never be instance of Class">variable instanceof Class</error>;
    //@ invariant <error descr="Expression of type Test can never be instance of Test2">variable instanceof Test2</error>;
    //@ invariant new Test() instanceof JavaInstanceofAndCasting;
    //@ invariant new JavaInstanceofAndCasting() instanceof Test;
    //@ invariant <error descr="Expression of type JavaInstanceofAndCasting can never be instance of Test2">new JavaInstanceofAndCasting() instanceof Test2</error>;
    //@ invariant new Object() instanceof Test;
    //@ invariant <error descr="Expression of type Test2 can never be instance of Test">new Test2() instanceof Test</error>;

    /*@pure*/int getZero() {
        return 0;
    }

    private class Test extends JavaInstanceofAndCasting {

    }

    private class Test2 {

    }
}


