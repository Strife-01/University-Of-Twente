package ss.hotel;

public class Safe {
    private boolean safeDoor; // true if open, false if closed
    private boolean safeActivated; // true if activated, false if deactivated

    public Safe() {
        this.safeDoor = false;
        this.safeActivated = false;
    }

    public void activate() {
        this.safeActivated = true;
    }

    public void deactivate() {
        close();
        this.safeActivated = false;
    }

    public void open() {
        if (this.safeActivated) {
            this.safeDoor = true;
        }
    }

    public void close() {
        this.safeDoor = false;
    }

    public boolean isActive() {
        return this.safeActivated;
    }

    public boolean isOpen() {
        return this.safeDoor;
    }
}
