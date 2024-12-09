package typeAnnotatorTestData;

public class SpecVisibilityAcrossClasses {
    SpecVisibilityAcrossClassesOtherClass other = new SpecVisibilityAcrossClassesOtherClass();

    //@ invariant <error descr="Reference cannot be resolved">other.private_field</error>;
    //@ invariant other.spec_public_field;
    //@ invariant other.spec_protected_field;

    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">other.private_method()</error>;
    //@ invariant other.spec_public_method();
    //@ invariant other.spec_protected_method();
    //@ invariant new SpecVisibilityAcrossClassesOtherClass(0).spec_public_field;
}

class SpecVisibilityAcrossClassesOtherClass {
    //@ spec_public
    private boolean spec_public_field;
    //@ spec_protected
    private boolean spec_protected_field;
    private boolean private_field;

    /*@ pure */
    private boolean private_method() {
        return true;
    }

    //@ spec_public
    /*@ pure */
    private boolean spec_public_method() {
        return true;
    }

    //@ spec_protected
    /*@ pure */
    private boolean spec_protected_method() {
        return true;
    }

    //@ spec_protected
    private SpecVisibilityAcrossClassesOtherClass(int i) {

    }

    public SpecVisibilityAcrossClassesOtherClass() {

    }
}


