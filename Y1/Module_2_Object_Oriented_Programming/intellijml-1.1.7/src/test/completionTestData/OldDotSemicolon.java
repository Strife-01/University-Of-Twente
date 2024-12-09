package completionTestData;

import java.util.ArrayList;

public class OldDotSemicolon {

    public ArrayList<Integer> list = new ArrayList<>();


    /*@
        requires \old(list).<caret>;
    */
    public int getNumber() {
        return 7;
    }
}
