package typeAnnotatorTestData;

public class BackslashResult {

    //@ ensures <error descr="This must be of type boolean, but is int">\result</error>;
    int getInt() {
        return 0;
    }

    //@ ensures <error descr="This must be of type boolean, but is Object">\result</error>;
    Object getObject() {
        return new Object();
    }

    //@ ensures <error descr="This must be of type boolean, but is String">\result</error>;
    String getString() {
        return "";
    }

    //@ ensures <error descr="This must be of type boolean, but is char">\result</error>;
    char getChar() {
        return 'c';
    }

    //@ ensures \result;
    boolean getBool() {
        return true;
    }

    //@ ensures <error descr="Cannot use \result here, as this method / constructor does not return anything">\result</error>;
    void getVoid() {
        return;
    }
}
