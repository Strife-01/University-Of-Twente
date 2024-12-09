package completionTestData;

public class CodeBlock {

    public int number = 5;

    public int getNumber() {
        int num = 5;
        if (number == 0) {
            int visible = 7;

            if (number == 7) {
                int notVisible = 8;
                num++;
            }

            //@ assert <caret>
        }
        for (int i = 0; i < 10; i++) {
            num++;
        }
        return num;
    }

    public int getRandomNumber() {
        return 4;
    }

}
