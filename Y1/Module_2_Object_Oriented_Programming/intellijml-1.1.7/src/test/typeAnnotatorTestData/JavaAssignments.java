package typeAnnotatorTestData;

public class JavaAssignments {
    int x = 0;
    Object obj = new Object();
    JavaAssignments assignments = new JavaAssignments();
    final boolean bool = false;

    // should give error for not being pure
    //@ invariant (<error descr="JML expressions should be pure and assignments are not pure">x = 4</error>) > 5;
    //@ invariant (<error descr="JML expressions should be pure and assignments are not pure">obj = new Object()</error>) > 5;

    public void test(int i) {
        int y = 7;
        // should give error for not being pure
        //@ assert (<error descr="JML expressions should be pure and assignments are not pure">y = 9</error>) == 8;
        //@ assert (<error descr="JML expressions should be pure and assignments are not pure">i = 9</error>) == 8;

        //@ loop_invariant (<error descr="JML expressions should be pure and assignments are not pure">j = 8</error>) == 10;
        for (int j = 0; j < 10; j++) {

        }
    }
}
