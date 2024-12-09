package ss.week5;

public class TooFewArgumentsException extends WrongArgumentException {
    public TooFewArgumentsException(String message) {
        super(message);
    }
    public TooFewArgumentsException() {
        this("too few arguments");
    }

}
