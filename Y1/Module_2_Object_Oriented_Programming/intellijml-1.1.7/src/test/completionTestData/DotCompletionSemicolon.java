package completionTestData;

import java.util.ArrayList;

public class DotCompletionSemicolon {

    public ArrayList<Integer> numbers = new ArrayList<>();

    /*@
    requires numbers.<caret>;
    */
    public int getInt(int methodParameter) {
        return methodParameter;
    }

}
