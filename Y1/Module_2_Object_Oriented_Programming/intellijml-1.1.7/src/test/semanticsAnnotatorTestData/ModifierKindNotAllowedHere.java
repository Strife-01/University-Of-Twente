package semanticsAnnotatorTestData;

//@ spec_public
//@ pure
//@ <error descr="Modifier 'instance' is not allowed above a class">instance</error>
//@ <error descr="Modifier 'helper' is not allowed above a class">helper</error>
//@ <error descr="Modifier 'nullable' is not allowed above a class">nullable</error>
//@ <error descr="Modifier 'public' is not allowed above a class">public</error>
//@ <error descr="Modifier 'protected' is not allowed above a class">protected</error>
//@ <error descr="Modifier 'private' is not allowed above a class">private</error>
//@ <error descr="Modifier 'static' is not allowed above a class">static</error>
public class ModifierKindNotAllowedHere {
    //@ <error descr="Modifier 'spec_public' is not allowed before a class_invariant">spec_public</error> invariant 1 > 0;
    //@ <error descr="Modifier 'spec_protected' is not allowed before a class_invariant">spec_protected</error> invariant 1 > 0;
    //@ <error descr="Modifier 'pure' is not allowed before a class_invariant">pure</error> invariant 1 > 0;
    //@ instance invariant 1 > 0;
    //@ <error descr="Modifier 'helper' is not allowed before a class_invariant">helper</error> invariant 1 > 0;
    //@ <error descr="Modifier 'nullable' is not allowed before a class_invariant">nullable</error> invariant 1 > 0;
    //@ public invariant 1 > 0;
    //@ private invariant 1 > 0;
    //@ protected invariant 1 > 0;
    //@ static invariant 1 > 0;

    //@ spec_protected
    //@ <error descr="Modifier 'pure' is not allowed above a field">pure</error>
    //@ instance
    //@ <error descr="Modifier 'helper' is not allowed above a field">helper</error>
    //@ nullable
    //@ <error descr="Modifier 'public' is not allowed above a field">public</error>
    //@ <error descr="Modifier 'private' is not allowed above a field">private</error>
    //@ <error descr="Modifier 'protected' is not allowed above a field">protected</error>
    //@ <error descr="Modifier 'static' is not allowed above a field">static</error>
    public int x = 10;

    //@ spec_protected
    //@ pure
    //@ <error descr="Modifier 'instance' is not allowed above a constructor">instance</error>
    //@ helper
    //@ <error descr="Modifier 'nullable' is not allowed above a constructor">nullable</error>
    //@ <error descr="Modifier 'public' is not allowed above a constructor">public</error>
    //@ <error descr="Modifier 'private' is not allowed above a constructor">private</error>
    //@ <error descr="Modifier 'protected' is not allowed above a constructor">protected</error>
    //@ <error descr="Modifier 'static' is not allowed above a constructor">static</error>
    public ModifierKindNotAllowedHere() {

    }

    //@ spec_protected
    //@ pure
    //@ <error descr="Modifier 'instance' is not allowed above a method">instance</error>
    //@ helper
    //@ nullable
    //@ <error descr="Modifier 'public' is not allowed above a method">public</error>
    //@ <error descr="Modifier 'private' is not allowed above a method">private</error>
    //@ <error descr="Modifier 'protected' is not allowed above a method">protected</error>
    //@ <error descr="Modifier 'static' is not allowed above a method">static</error>
    public int divX(int /*@ <error descr="Modifier 'spec_public' is not allowed before a parameter">spec_public</error>; <error descr="Modifier 'spec_protected' is not allowed before a parameter">spec_protected</error>; <error descr="Modifier 'pure' is not allowed before a parameter">pure</error>; <error descr="Modifier 'instance' is not allowed before a parameter">instance</error>; <error descr="Modifier 'helper' is not allowed before a parameter">helper</error>; nullable; <error descr="Modifier 'public' is not allowed before a parameter">public</error>; <error descr="Modifier 'private' is not allowed before a parameter">private</error>; <error descr="Modifier 'protected' is not allowed before a parameter">protected</error>; <error descr="Modifier 'static' is not allowed before a parameter">static</error>;*/ y) {

        //@ <error descr="Modifier 'spec_public' is not allowed above a variable declaration">spec_public</error>
        //@ <error descr="Modifier 'pure' is not allowed above a variable declaration">pure</error>
        //@ <error descr="Modifier 'instance' is not allowed above a variable declaration">instance</error>
        //@ <error descr="Modifier 'helper' is not allowed above a variable declaration">helper</error>
        //@ nullable
        //@ <error descr="Modifier 'public' is not allowed above a variable declaration">public</error>
        //@ <error descr="Modifier 'private' is not allowed above a variable declaration">private</error>
        //@ <error descr="Modifier 'protected' is not allowed above a variable declaration">protected</error>
        //@ <error descr="Modifier 'static' is not allowed above a variable declaration">static</error>
        int z;

        return y / x;
    }
}
