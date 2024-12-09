package completionTestData;

import java.util.AbstractList;

public class Super extends AbstractList<Integer> {

    /*@
        requires super.<caret>
    */
    public int getRandomNumber() {
        return 1;
    }

    @Override
    public Integer get(int index) {
        return null;
    }

    @Override
    public int size() {
        return 0;
    }
}
