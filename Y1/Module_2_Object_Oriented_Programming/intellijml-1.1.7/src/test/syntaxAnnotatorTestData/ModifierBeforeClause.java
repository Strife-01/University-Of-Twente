package syntaxAnnotatorTestData;

public class ModifierBeforeClause {
    /*@
            helper;
                    pure;
        <error descr="All specification cases must be placed before any modifiers">requires</error> b!=0;
            ensures \result ==a/b;
    */
    public int div(int a, int b) {
        return a / b;
    }
}
