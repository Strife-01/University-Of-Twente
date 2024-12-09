package ss.hotel;

import java.util.Objects;

public class Hotel {
    protected String name;
    protected Room[] rooms;
    final protected int NUMBER_OF_ROOMS = 2;

    /*@
        protected invariant name != "";
    */

    /**
     * Creates a hotel object.
     *
     * @param name the name of the hotel
     */
    /*@
        requires name != null && name != "";
        ensures this.name != null;
        ensures this.name == name;
        ensures (\forall int i; i < this.NUMBER_OF_ROOMS; this.rooms[i] != null);
    */
    public Hotel(String name) {
        this.name = name;
        rooms = new Room[this.NUMBER_OF_ROOMS];
        for (int i = 0; i < this.NUMBER_OF_ROOMS; i++) {
            this.rooms[i] = new Room(i);
        }
    }

    /**
     * Gets the name of the hotel.
     *
     * @return name of hotel
     */
    /*@
        ensures this.name != null;
        pure
    */
    public String getName() {
        return this.name;
    }

    /**
     * Check if the guest with provided name is in the hotel.
     *
     * @param name user we check
     * @return true if the user is in the hotel or false
     */
    /*@
        requires name != "";
    */
    public boolean isCheckedIn(String name) {
        for (int i = 0; i < this.NUMBER_OF_ROOMS; i++) {
            if (this.rooms[i] != null && this.rooms[i].getGuest() != null &&
                    Objects.equals(this.rooms[i].getGuest().getName(), name)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Retrieves the room in which the guest is checked in or null.
     *
     * @param name the name of the user in question
     * @return room in which the user is stationed or null
     */
    /*@
        requires name != "null";
        ensures (\forall int i; i < this.NUMBER_OF_ROOMS; this.rooms[i].getGuest().getName().equals(name));
    */
    public Room getRoom(String name) {
        for (int i = 0; i < this.NUMBER_OF_ROOMS; i++) {
            if (this.rooms[i].getGuest() != null &&
                    this.rooms[i].getGuest().getName().equals(name)) {
                return this.rooms[i];
            }
        }
        return null;
    }

    /**
     * Get a free room in the hotel.
     * @return free room or null
     */
    public Room getFreeRoom() {
        for (int i = 0; i < this.NUMBER_OF_ROOMS; i++) {
            if (this.rooms[i].getGuest() == null) {
                return this.rooms[i];
            }
        }
        return null;
    }

    /**
     * If the user is not already checked in and there are free rooms, we check the guest in.
     *
     * @param name name of the guest
     * @return the room in which the guest will stay or null
     */
    /*@
        requires name != "";
    */
    public Room checkIn(String name) {
        // Check if current guest is checked in
        if (getRoom(name) != null) {
            return null;
        }
        // Check the guest in or return null
        Room r = getFreeRoom();
        if (r != null) {
            Guest g = new Guest(name);
            g.checkin(r);
            r.setGuest(g);
            return r;
        }
        return null;
    }

    /**
     * Checkes out a guest if they are present in the hotel.
     * @param name of guest
     */
    /*@
        requires name != "";
    */
    public boolean checkOut(String name) {
        Room r = getRoom(name);
        if (r == null) {
            return false;
        }

        r.getSafe().deactivate();
        return r.getGuest().checkout();
    }

    public String toString() {
        String output = "";
        for (int i = 0; i < this.NUMBER_OF_ROOMS; i++) {
            output += "\tRoom " + this.rooms[i].getNumber() + ": \n";
            if (this.rooms[i].getGuest() != null) {
                output += "\t\trented by: Guest " + this.rooms[i].getGuest().getName() + "\n";
            } else {
                output += "\t\tnot rented\n";
            }
            output += "\t\tsafe active: " + this.rooms[i].getSafe().isActive() + "\n";
        }
        return output;
    }
}
