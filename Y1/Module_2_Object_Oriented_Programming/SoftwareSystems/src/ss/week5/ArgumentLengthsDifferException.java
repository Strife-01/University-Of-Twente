package ss.week5;

public class ArgumentLengthsDifferException extends WrongArgumentException {
    public ArgumentLengthsDifferException(int len1, int len2) {
        super("error: length of command line arguments " + "differ (" + len1 + ", " + len2 + ")");
    }
    public ArgumentLengthsDifferException(String message) {
        super(message);
    }
}
