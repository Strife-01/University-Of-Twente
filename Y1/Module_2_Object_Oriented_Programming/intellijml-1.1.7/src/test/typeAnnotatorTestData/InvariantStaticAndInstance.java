package typeAnnotatorTestData;

public class InvariantStaticAndInstance {
    boolean instanceBool = true;
    static boolean staticBool = true;

    /*@pure*/ boolean instanceMethod() {
        return true;
    }

    /*@pure*/
    static boolean staticMethod() {
        return true;
    }

    //@ invariant instanceBool;
    //@ invariant instanceMethod();
    //@ invariant staticBool;
    //@ invariant staticMethod();
    //@ static invariant <error descr="A static invariant can only see static fields">instanceBool</error>;
    //@ static invariant <error descr="A static invariant can only see static fields">instanceMethod()</error>;
    //@ static invariant staticBool;
    //@ static invariant staticMethod();
    //@ instance invariant instanceBool;
    //@ instance invariant instanceMethod();
    //@ instance invariant staticBool;
    //@ instance invariant staticMethod();
}

interface InvariantStaticAndInstanceInterface {
    boolean inferredStaticBool = true;
    static boolean explicitStaticBool = true;

    /*@pure*/ boolean instanceMethod();

    /*@pure*/
    static boolean staticMethod() {
        return true;
    }

    ;

    //@ invariant inferredStaticBool;
    //@ invariant explicitStaticBool;
    //@ static invariant inferredStaticBool;
    //@ static invariant explicitStaticBool;
    //@ instance invariant inferredStaticBool;
    //@ instance invariant explicitStaticBool;

    //@ invariant <error descr="A static invariant can only see static fields">instanceMethod()</error>;
    //@ invariant staticMethod();
    //@ static invariant <error descr="A static invariant can only see static fields">instanceMethod()</error>;
    //@ static invariant staticMethod();
    //@ instance invariant instanceMethod();
    //@ instance invariant staticMethod();
}
