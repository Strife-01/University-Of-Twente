package completionTestData;

import static java.lang.Integer.MAX_VALUE;

public class SpecificStaticImport {

    /*@
        requires <caret>
    */
    public int getRandomNumber() {
        int number = MAX_VALUE;
        return 0;
    }

}
