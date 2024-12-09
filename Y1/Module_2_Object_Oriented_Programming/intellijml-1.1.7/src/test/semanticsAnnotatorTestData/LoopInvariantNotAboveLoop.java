package semanticsAnnotatorTestData;

public class LoopInvariantNotAboveLoop {
    private int number = 10;

    public void loop() {
        int i = 10;
        //@ maintaining i < 10;
        while (i > 0) {
            i--;
        }

        //@ loop_invariant j >= 0;
        for (int j = 0; j < 10; j++) {
            System.out.println(j);
        }

        String testString = "This is a test string";
        int count = 0;
        //@ maintaining count >= 0;
        for (String sub : testString.split(" ")) {
            System.out.println(sub);
            count++;
        }

        //@ <error descr="loop_invariant / maintaining needs to be above a loop">loop_invariant x <= 10;</error>

        int x = 10;
        //@ loop_invariant x <= 10;
        do {
            x--;
        } while (x > 0);
    }
}