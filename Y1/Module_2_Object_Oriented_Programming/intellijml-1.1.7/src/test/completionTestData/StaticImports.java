package completionTestData;

import static java.lang.Integer.*;

public class StaticImports {

    /*@
    requires <caret>
    */
    public int getInt(int methodParameter) {
        return methodParameter;
    }
}
