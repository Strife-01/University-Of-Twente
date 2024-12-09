package completionTestData;

public class This {

    private int privateNum = 1;
    protected int protectedNum = 2;
    public int publicNum = 3;
    int defaultNum = 4;

    /*@
    requires this.<caret>
    */
    public int getSomething() {
        return 5;
    }

    private int getPrivateNum() {
        return privateNum;
    }

    protected int getProtectedNum() {
        return protectedNum;
    }

    public int getPublicNum() {
        return publicNum;
    }

    int getDefaultNum() {
        return defaultNum;
    }
}
