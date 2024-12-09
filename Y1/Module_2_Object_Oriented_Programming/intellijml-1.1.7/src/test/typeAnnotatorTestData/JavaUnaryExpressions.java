package typeAnnotatorTestData;

public class JavaUnaryExpressions {
    int i = 0;
    boolean b = true;
    float f = 1.2f;

    // correct expressions
    /*@ invariant i++ == 0;
      @ invariant ++i == 0;
      @ invariant i-- == 0;
      @ invariant --i == 0;
      @ invariant -i == 0;
      @ invariant +i == 0;
      @ invariant !b;
      (* ++ should be allowed on a float *)
      @ invariant f++ == 0;
    */

    // wrong types
    /*@ invariant <error descr="The operator '++' is not applicable to an operand of type boolean">b++</error> == 0;
      @ invariant <error descr="The operator '++' is not applicable to an operand of type boolean">++b</error> == 0;
      @ invariant <error descr="The operator '--' is not applicable to an operand of type boolean">b--</error> == 0;
      @ invariant <error descr="The operator '--' is not applicable to an operand of type boolean">--b</error> == 0;
      @ invariant <error descr="The operator '-' is not applicable to an operand of type boolean">-b</error> == 0;
      @ invariant <error descr="The operator '+' is not applicable to an operand of type boolean">+b</error> == 0;
      @ invariant <error descr="The operator '!' is not applicable to an operand of type int">!i</error>;
    */

    // on values instead of references, should not be allowed on ++ && --
    /*@ invariant <error descr="Variable expected">3++</error> == 0;
      @ invariant <error descr="Variable expected">++3</error> == 0;
      @ invariant <error descr="Variable expected">3--</error> == 0;
      @ invariant <error descr="Variable expected">--3</error> == 0;
      @ invariant -3 == 0;
      @ invariant +3 == 0;
      @ invariant !true;
      @ invariant <error descr="Variable expected">1.3++</error> == 0;
      @ invariant <error descr="Variable expected">getInt()++</error> == 0;
    */

    //@pure
    int getInt() {
        return 5;
    }
}
