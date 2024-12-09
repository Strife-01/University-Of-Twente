package ss.hotel;

import ss.hotel.Safe;

public class Room {
    private int number;
    private Guest guest;
    private Safe safe;

    /**
     * Creates a <code>Room</code> with the given number, without a guest.
     * @param no number of the new <code>Room</code>
     */

    public Room(int number, Safe safe) {
        this.number = number;
        this.safe = safe;
    }

    public Room(int number) {
        this(number, new Safe());
    }

    /**
     * Returns the number of this Room.
     */
    /*@
        pure
    */
    public int getNumber() {
    	return number;
    }

    /**
     * Returns the current guest living in this Room.
     * @return the guest of this Room, null if not rented
     */
    /*@
        pure
    */
    public Guest getGuest() {
    	return guest;
    }

    /*@
        pure
    */
    public Safe getSafe() {
        return this.safe;
    }

    /**
     * Assigns a Guest to this Room.
     * @param guest the new guest renting this Room, if null is given, Room is empty afterwards
     */
    public void setGuest(Guest guest) {
    	this.guest = guest;
    }

    // Override the toString method
    public String toString () {
        if (this.guest != null) {
            return "Room " + this.number + " with guest " + this.guest.getName();
        }
        return "Room " + this.number + " with guest " + this.guest;
    }
}
