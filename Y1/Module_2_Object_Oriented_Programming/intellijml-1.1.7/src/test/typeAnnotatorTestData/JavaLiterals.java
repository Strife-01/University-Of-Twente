package typeAnnotatorTestData;

public class JavaLiterals {

    //@ invariant false;
    //@ invariant true;
    //@ invariant 'c' > 'A' ;
    //@ invariant 'c' > <error descr="A char must end with '">'A</error>;
    //@ invariant <error descr="Not a valid expression">c' > 'A'</error>;
    //@ invariant 0 > -1d;
    //@ invariant 0.1 > -0.1;
    //@ invariant 0.1f > -0.1d;
    //@ invariant <error descr="Not a valid expression">0.1L > 1L</error>;
    //@ invariant 1L > 7;
    //@ invariant 1L > 7;
    // error because 8 is not allowed in octal
    //@ invariant 0b001 > <error descr="Incorrect syntax">0847</error>;
    //@ invariant 0xABc > 077;
    // invalid because G is not allowed in hex
    //@ invariant <error descr="Not a valid expression">0xGF > 077</error>;
    // binary cannot contain 2;
    //@ invariant <error descr="Incorrect syntax">0b0020</error> > 1;
    // integer cannot have letters
    //@ invariant <error descr="Not a valid expression">34a5 > 1</error>;
}
