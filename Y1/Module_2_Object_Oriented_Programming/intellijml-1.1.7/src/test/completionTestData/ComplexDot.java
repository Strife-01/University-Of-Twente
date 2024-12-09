package completionTestData;

import java.util.ArrayList;

public class ComplexDot {

    public ArrayList<Integer> numbers = new ArrayList<>();

    /*@
        requires numbers.get(0).toBinaryString(123).<caret>
    */
    public int getRandomNumber() {
        return 0;
    }

}
