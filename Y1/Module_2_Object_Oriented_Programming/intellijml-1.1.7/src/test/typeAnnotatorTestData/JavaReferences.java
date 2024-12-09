package typeAnnotatorTestData;

public class JavaReferences {
    private int num = 5;

    //@ private invariant num > 0;
    //@ invariant sumNum(5) > 0;

    // with an inner class
    //@ invariant <error descr="Reference cannot be resolved">Inner.testNum</error> > 0;
    //@ invariant new Inner().testNum > 0;
    //@ invariant <error descr="Reference cannot be resolved">Inner.publicTestNum</error> > 0;
    //@ invariant new Inner().publicTestNum > 0;
    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">Inner.getTestNum()</error> > 0;
    //@ invariant new Inner().getTestNum() > 0;

    // with a different class
    //@ invariant <error descr="Reference cannot be resolved">JavaReferencesTest.testNum</error> > 0;
    //@ invariant <error descr="Reference cannot be resolved">new JavaReferencesTest().testNum</error> > 0;
    //@ invariant JavaReferencesTest.publicStaticTestNum > 0;
    //@ invariant new JavaReferencesTest().publicStaticTestNum > 0;
    //@ invariant <error descr="Reference cannot be resolved">JavaReferencesTest.staticTestNum</error> > 0;
    //@ invariant <error descr="Reference cannot be resolved">new JavaReferencesTest().staticTestNum</error> > 0;
    //@ invariant <error descr="Reference cannot be resolved">JavaReferencesTest.protectedTestNum</error> > 0;
    //@ invariant new JavaReferencesTest().protectedTestNum > 0;
    //@ invariant <error descr="Method could not be resolved, maybe the parameters do not correspond?">JavaReferencesTest.getTestNum()</error> > 0;
    //@ invariant new JavaReferencesTest().getTestNum() > 0;

    //@ invariant <error descr="Reference cannot be resolved">nonExistent</error> > 0;

    // chains
    /*@ invariant <error descr="Reference cannot be resolved">new Inner().obj.a</error>.b.c == null;
      @ invariant <error descr="Reference cannot be resolved">b</error>.c.d == null;
    */

    // multiple variables in a forall
    //@ invariant (\forall int x, y; 0 <= x && x < y && y < 100; x + y == 100);

    /*@ (* parameters accessible *)
      @ ensures a > 0;
      @ (* no local variables accessible *)
      @ ensures <error descr="Reference cannot be resolved">b</error> > 0;
    */
    /*@pure*/int sumNum(int a) {
        int b = 8;
        // local variable and parameter accessible
        //@ assert b > a;
        // class variables accessible
        //@ assert num >= 5;

        // for loop invariants, loop initializer is also reachable
        //@ loop_invariant i >= 0 && a > 0 && b > 0;
        //@ assert <error descr="Reference cannot be resolved">i</error> >= 0;
        for (int i = 0; i < 10; i++) {
            int x = 9;
        }

        return a + num;
    }

    private class Inner {
        private int testNum = 10;
        public int publicTestNum = 15;
        Object obj;

        /*@pure*/
        protected int getTestNum() {
            // access variable from outer class
            //@ assert num >= 5;
            return testNum;
        }
    }
}

class JavaReferencesTest {
    private int testNum = 10;
    private static int staticTestNum = 15;
    public static int publicStaticTestNum = 20;
    protected int protectedTestNum = 25;

    /*@pure*/
    protected int getTestNum() {
        return testNum;
    }
}
