package completionTestData;

import java.util.ArrayList;

public class ResultDotSemicolon {

    /*@
        ensures \result.<caret>;
    */
    public ArrayList<Integer> getRandomArray() {
        return new ArrayList<>();
    }
}
