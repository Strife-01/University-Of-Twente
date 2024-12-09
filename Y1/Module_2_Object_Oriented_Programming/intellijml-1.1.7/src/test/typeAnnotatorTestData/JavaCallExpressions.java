package typeAnnotatorTestData;

public class JavaCallExpressions {
    private int num;

    // using wrong amount of arguments
    //@ invariant getNum() > 0;
    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">getNum(1)</error> > 0;
    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">sumNum()</error> > 0;
    //@ invariant sumNum(2) > 0;
    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">sumNum(2,3)</error> > 0;

    // using wrong argument types
    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">sumNum(true)</error> > 0;
    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">sumNum("String")</error> > 0;

    // using ... parameter
    //@ invariant concat() == null;
    //@ invariant concat(null) == null;
    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">concat(10)</error> == null;
    //@ invariant concat("test") == null;
    //@ invariant concat("test","test2") == null;

    // overloading
    //@ invariant overload(7);
    //@ invariant overload("string");
    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">overload(new Object())</error>;
    //@ invariant overload("string",10);

    /*@pure*/int getNum() {
        return num;
    }

    /*@pure*/int sumNum(int i) {
        return num + i;
    }

    /*@pure*/ String concat(String... strs) {
        StringBuilder result = new StringBuilder("");
        for (String str : strs) {
            result.append(str);
        }
        return result.toString();
    }

    /*@pure*/boolean overload(int i) {
        return false;
    }

    /*@pure*/boolean overload(String i) {
        return false;
    }

    /*@pure*/boolean overload(String str, int i) {
        return false;
    }

}
