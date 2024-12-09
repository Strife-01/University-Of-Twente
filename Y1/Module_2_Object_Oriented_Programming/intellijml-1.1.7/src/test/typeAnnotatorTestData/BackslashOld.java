package typeAnnotatorTestData;

public class BackslashOld {

    /*@ ensures \old(true);
      @ ensures <error descr="Reference cannot be resolved">\old(number)</error>;
      @ ensures <error descr="Reference cannot be resolved">\old(nonExistantVar)</error>;
      @ ensures <error descr="This must be of type boolean, but is Object">\old(new Object())</error>;
      @ ensures <error descr="This must be of type boolean, but is int">\old(getInt())</error>;
      @ pure
    */
    int getInt() {
        return 0;
    }
}
