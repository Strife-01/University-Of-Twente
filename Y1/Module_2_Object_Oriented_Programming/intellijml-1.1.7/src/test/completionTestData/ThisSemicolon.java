package completionTestData;

public class ThisSemicolon {

    private int privateNum = 1;
    protected int protectedNum = 2;
    public int publicNum = 3;
    int defaultNum = 4;

    /*@
    requires this.<caret>;
    */
    public int getSomething() {
        return 5;
    }

    public int getPrivateNum() {
        return privateNum;
    }

    public int getProtectedNum() {
        return protectedNum;
    }

    public int getPublicNum() {
        return publicNum;
    }

    public int getDefaultNum() {
        return defaultNum;
    }
}
