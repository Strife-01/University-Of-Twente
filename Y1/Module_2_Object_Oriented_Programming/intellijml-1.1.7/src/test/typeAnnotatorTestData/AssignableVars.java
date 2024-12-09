package typeAnnotatorTestData;

import java.util.List;

public class AssignableVars extends Test {
    private int b;
    private int[] intArr = new int[]{1, 2, 3, 4, 5};
    private final int z = 5;

    private List<String> strList;
    private Test testRef = new Test();

    /*@ assignable (* just wrong *)
        <error descr="Reference cannot be resolved">b.x</error>,
        <error descr="This cannot be assigned">Test</error>,
        <error descr="This is not a correct reference">int</error>;
    */
    /*@ assignable (* variable references, some are final *)
        <error descr="Reference cannot be resolved">a</error>,
        b,
        testRef,
        intArr,
        Test.five,
        <error descr="This variable is final, so cannot be assigned">z</error>,
        <error descr="This variable is final, so cannot be assigned">Test.Inner.inner</error>, (* fields in interfaces are always final *)
        <error descr="Reference cannot be resolved">AssignableVars.b</error>; (* not static *)
    */
    /*@ assignable (* '.*' is only allowed on classes or references to classes *)
      this.*,
      Test.*,
      Test.Inner.*,
      <error descr="You can only use '.*' on classes and interfaces">intArr.*</error>,
      testRef.*,
      <error descr="You can only use '.*' on classes and interfaces">b.*</error>;
    */
    /*@ assignable (* '[*]' is only allowed on arrays *)
        <error descr="You can only use '[*]' on arrays">this[*]</error>,
        <error descr="You can only use '[*]' on arrays">Test[*]</error>,
        intArr[*],
        testRef.objArr[*],
        <error descr="You can only use '[*]' on arrays">strList[*]</error>;
    */
    /*@ assignable (* trying references with 'this' *)
        <error descr="This cannot be assigned">this</error>,
        this.*,
        this.b,
        this.five,
        this.intArr[*],
        this.testRef.*,
        <error descr="This is not a correct reference">this.this</error>;
    */
    /*@ assignable (* trying references with 'super' *)
        <error descr="This cannot be assigned">super</error>,
        super.*,
        super.five,
        super.objArr[*],
        <error descr="Reference cannot be resolved">super.Inner.*</error>,
        <error descr="This is not a correct reference">super.this</error>;
    */
    public int div(int a, int b) throws ArithmeticException {
        int c = 5;
        return a / b;
    }
}

class Test {
    public static int five = 5;
    public Object[] objArr;

    public interface Inner {
        boolean inner = true;
    }
}
