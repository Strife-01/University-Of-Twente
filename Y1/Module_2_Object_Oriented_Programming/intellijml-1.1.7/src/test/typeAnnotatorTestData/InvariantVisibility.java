package typeAnnotatorTestData;

public class InvariantVisibility {
    public boolean public_field;
    protected boolean protected_field;
    boolean default_field;
    private boolean private_field;

    //@ spec_public
    private boolean spec_public_field;
    //@ spec_protected
    private boolean spec_protected_field;

    /*@ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">public_field</error>;
      @ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">protected_field</error>;
      @ invariant default_field;
      @ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">private_field</error>;
      @ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_public_field</error>;
      @ invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_protected_field</error>;
    */

    /*@ public invariant public_field;
      @ public invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">protected_field</error>;
      @ public invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">default_field</error>;
      @ public invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">private_field</error>;
      @ public invariant spec_public_field;
      @ public invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_protected_field</error>;
    */

    /*@ protected invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">public_field</error>;
      @ protected invariant protected_field;
      @ protected invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">default_field</error>;
      @ protected invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">private_field</error>;
      @ protected invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_public_field</error>;
      @ protected invariant spec_protected_field;
    */

    /*@ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">public_field</error>;
      @ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">protected_field</error>;
      @ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">default_field</error>;
      @ private invariant private_field;
      @ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_public_field</error>;
      @ private invariant <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">spec_protected_field</error>;
    */
}
