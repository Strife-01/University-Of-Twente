package typeAnnotatorTestData;

public class InvariantVisibilityMethods {
    /*@ pure */
    public boolean public_method() {
        return true;
    }

    /*@ pure */
    protected boolean protected_method() {
        return true;
    }

    /*@ pure */
    boolean default_method() {
        return true;
    }

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

    /*@ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">public_method()</error>;
      @ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">protected_method()</error>;
      @ invariant default_method();
      @ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">private_method()</error>;
      @ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_public_method()</error>;
      @ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_protected_method()</error>;
    */

    /*@ public invariant public_method();
      @ public invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">protected_method()</error>;
      @ public invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">default_method()</error>;
      @ public invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">private_method()</error>;
      @ public invariant spec_public_method();
      @ public invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_protected_method()</error>;
    */

    /*@ protected invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">public_method()</error>;
      @ protected invariant protected_method();
      @ protected invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">default_method()</error>;
      @ protected invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">private_method()</error>;
      @ protected invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_public_method()</error>;
      @ protected invariant spec_protected_method();
    */

    /*@ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">public_method()</error>;
      @ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">protected_method()</error>;
      @ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">default_method()</error>;
      @ private invariant private_method();
      @ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_public_method()</error>;
      @ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_protected_method()</error>;
    */
}
