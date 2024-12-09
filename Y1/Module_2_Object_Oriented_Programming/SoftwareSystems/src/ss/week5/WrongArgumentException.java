package ss.week5;

public class WrongArgumentException extends Exception {
    public WrongArgumentException(String message) {
        super(message);
    }
    public WrongArgumentException() {this("Wrong args");}
}
