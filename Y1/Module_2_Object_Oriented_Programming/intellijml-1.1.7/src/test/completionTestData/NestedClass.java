package completionTestData;

public class NestedClass {

    public int publicInt = 0;
    protected int protectedInt = 1;
    int defaultInt = 2;
    private int privateInt = 3;

    public int getPublicInt() {
        return publicInt;
    }

    protected int getProtectedInt() {
        return protectedInt;
    }

    int getDefaultInt() {
        return defaultInt;
    }

    private int getPrivateInt() {
        return privateInt;
    }

    public class publicInnerClass {

        private int innerClassInt = 4;

        /*@
            requires <caret>
        */
        public int getRandomNumber() {
            return 0;
        }

    }

}
