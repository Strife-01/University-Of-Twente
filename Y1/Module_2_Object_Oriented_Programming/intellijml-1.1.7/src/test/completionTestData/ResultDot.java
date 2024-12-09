package completionTestData;

import java.util.ArrayList;

public class ResultDot {

    /*@
        ensures \result.<caret>
    */
    public ArrayList<Integer> getRandomArray() {
        return new ArrayList<>();
    }
}
