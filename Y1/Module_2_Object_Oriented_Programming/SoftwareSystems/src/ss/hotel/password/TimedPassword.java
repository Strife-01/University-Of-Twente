package ss.hotel.password;

// P3.21 in case that the password changer uses the testPassword function to check for the old
// password, then we would never be able to change the password ever again

import java.time.Instant;

public class TimedPassword extends Password {
    // time in milliseconds
    private Instant timestamp; // the last time the password was changed
    private int validTime;

    TimedPassword(int validTimeInMs) {
        super(new StrongChecker());
        this.timestamp = Instant.now();
        this.validTime = validTimeInMs;
    }

    TimedPassword() {
        this(5000);
    }

    public boolean isExpired() {
        Instant maxTime = timestamp.plusMillis(validTime);
        return maxTime.isBefore(Instant.now());
    }

    @Override
    public boolean setWord(String oldpass, String newpass) {
        if (super.setWord(oldpass, newpass)) {
            this.timestamp = Instant.now();
            return true;
        }
        return false;
    }
}
