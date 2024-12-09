package completionTestData;

import static java.lang.Integer.*;

public class StaticImportsSemicolon {

    /*@
    requires <caret>;
    */
    public int getInt(int methodParameter) {
        getInteger("5");
        return methodParameter;
    }
}
