package typeAnnotatorTestData;

public class BackslashTypeFunctions {
    // make the expressions not boolean on purpose so we can see that
    // the correct type is used internally by looking at the error messages

    int number = 5;

    //@ ensures <error descr="Reference cannot be resolved">\TYPE</error>;
    //@ ensures <error descr="This must be of type boolean, but is Class<Class>">\TYPE.class</error>;
    /*@ ensures <error descr="This must be of type boolean, but is Class<Integer>">\typeof(number)</error>;
      @ ensures <error descr="This must be of type boolean, but is Class<String>">\typeof("")</error>;
      @ ensures <error descr="This must be of type boolean, but is Class<BackslashTypeFunctions>">\typeof(new BackslashTypeFunctions())</error>;
      @ ensures \typeof(<error descr="Reference cannot be resolved">NonExistentClass</error>);
      @ ensures \typeof(<error descr="Reference cannot be resolved">nonExistentVar</error>);
      @ ensures <error descr="This must be of type boolean, but is Class<int[]>">\typeof(new int[5])</error>;
      @ ensures \typeof(<error descr="Reference cannot be resolved">\TYPE</error>);
    */
    /*@ ensures \elemtype(<error descr="This should be of type java.lang.Class, maybe you forgot to use .class or .getClass()?">new Object()</error>);
      @ ensures \elemtype(<error descr="This should be of type java.lang.Class, maybe you forgot to use .class or .getClass()?">number</error>);
      @ ensures \elemtype(<error descr="Reference cannot be resolved">nonExistentVar</error>.class);
      @ ensures <error descr="This must be of type boolean, but is Class<Integer>">\elemtype(\typeof(new int[5]))</error>;
      @ ensures <error descr="This must be of type boolean, but is Class<Integer>">\elemtype(int[].class)</error>;
      @ ensures <error descr="This must be of type boolean, but is Class<Integer>">\elemtype(new int[5].getClass())</error>;
      @ ensures \elemtype(<error descr="This is not an array">\type(Object)</error>);
      @ ensures \elemtype(<error descr="This is not an array">Object.class</error>);
      @ ensures \elemtype(<error descr="This is not an array">new Object().getClass()</error>);
      @ ensures \elemtype(<error descr="This is not an array">\TYPE.class</error>);
    */
    /*@ ensures \nonnullelements(new int[5]);
      @ ensures \nonnullelements(new int[5][][]);
      @ ensures \nonnullelements(<error descr="This is not an array">new Object()</error>);
      @ ensures \nonnullelements(<error descr="This is not an array">number</error>);
      @ ensures \nonnullelements(<error descr="Reference cannot be resolved">nonExistentVar</error>);
    */
    /*@ ensures \type(<error descr="This is not the name of a primitive type or a class">number</error>);
      @ ensures \type(<error descr="This is not the name of a primitive type or a class">nonExistentVar</error>);
      @ ensures \type(<error descr="This is not the name of a primitive type or a class">NonExistentClass</error>);
      @ ensures <error descr="This must be of type boolean, but is Class<BackslashTypeFunctions>">\type(BackslashTypeFunctions)</error>;
      @ ensures <error descr="This must be of type boolean, but is Class<Exception>">\type(Exception)</error>;
      @ ensures <error descr="This must be of type boolean, but is Class<Integer>">\type(int)</error>;
      @ ensures <error descr="This must be of type boolean, but is Class<Class>">\type(\TYPE)</error>;
      @ ensures <error descr="This must be of type boolean, but is Class<int[]>">\type(int[])</error>;
    */
    /*@ ensures \elemtype(\type(int[])) == \type(int);
      @ ensures \type(\TYPE) == \typeof(\type(int));
     */
    int getInt() {
        return 0;
    }
}
