package typeAnnotatorTestData;

public class JMLOperators {

    //@ ensures 1<error descr="This operator cannot be applied to type int and type int"> <==> </error>2;
    //@ ensures 1<error descr="This operator cannot be applied to type int and type int"> <== </error>2;
    //@ ensures 1<error descr="This operator cannot be applied to type int and type int"> <=!=> </error>2;
    //@ ensures 1<error descr="This operator cannot be applied to type int and type int"> ==> </error>2;
    //@ ensures true<error descr="This operator cannot be applied to type boolean and type char"> <==> </error>'c';
    //@ ensures 1.2f<error descr="This operator cannot be applied to type float and type boolean"> <== </error>true;
    //@ ensures new Object()<error descr="This operator cannot be applied to type Object and type int"> <=!=> </error>2;
    //@ ensures ""<error descr="This operator cannot be applied to type String and type JMLOperators"> ==> </error>new JMLOperators();
    //@ ensures true <==> true;
    //@ ensures true <=!=> true;
    //@ ensures true <== true;
    //@ ensures true ==> true;
    //@ ensures true ==> true <==> true <=!=> true <== true;
    int getInt() {
        return 0;
    }
}
