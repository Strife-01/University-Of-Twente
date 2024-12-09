package ss.hotel;

/**
 * The class represents a guest which will stay in the hotel and all of their actions in relation to
 * it.
 */
public class Guest {
    private String name;
    private Room room;

    /*@
        private invariant name != "";
    */

    /**
     * Creates a guest and assigns them aname.
     * @param name the name of the guest
     */
    /*@
        requires name != "";
        ensures this.name != null;
    */
    public Guest(String name) {
        this.name = name;
    }

    /**
     * Gets the name of the guest.
     * @return name of guest
     */
    /*@
        ensures \result != null;
        pure
    */
    public String getName() {
        return this.name;
    }

    /**
     * Gets the room in which the guest is stationed.
     * @return pointer towards the guest's room object
     */
    /*@
        ensures (this.room != null) ==> \result != null;
        pure
    */
    public Room getRoom() {
        return this.room;
    }

    /**
     * If the guest is not checked in already will check them in.
     * @param room pointer to the room to be assigned to guest
     * @return true if the guest has been checked in and false otherwise
     */
    /*@
        requires room != null;
        ensures this.room != null;
    */
    public boolean checkin(Room room) {
        if (room.getGuest() == null) {
            this.room = room;
            room.setGuest(this);
            return true;
        }
        return false;
    }

    /**
     * Checks out a guest if they are in a room.
     * @return true if the guest was checked out and false if no room was assigned initially
     */
    /*@
        ensures this.room == null;
    */
    public boolean checkout() {
        if (this.room == null) {
            return false;
        }
        this.room.setGuest(null);
        this.room = null;
        return true;
    }

    // Override the toString method
    public String toString () {
        if (this.room != null) {
            return "Guest " + this.name + " in room " + this.room.getNumber();
        }
        return "Guest " + this.name + " in room " + this.room;
    }
}
