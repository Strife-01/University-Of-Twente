package completionTestData;

import java.util.ArrayList;
import java.util.List;

public class MixedJMLJavaDot {

    public ArrayList<Integer> list = new ArrayList<>();

    /*@
        ensures \result.get(\old(list.get(0).toString().length())).trim().toLowerCase().<caret>
    */
    public List<String> getList() {
        return new ArrayList<String>();
    }

}
