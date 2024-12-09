package ss.week2.hotel.items;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.hotel.*;
import ss.hotel.bill.Bill;
import ss.hotel.bill.StringBillPrinter;
import ss.hotel.password.Password;

import static org.junit.jupiter.api.Assertions.*;

public class PricedHotelTest {
    /** Test variable for a <tt>Hotel</tt> object. */
    private PricedHotel hotel;
    private String correctPassword;
    private String wrongPassword;
    public static final String GUEST_NAME_1 = "Major Gowen";
    public static final String GUEST_NAME_2 = "Miss Tibbs";
    public static final String GUEST_NAME_3 = "Miss Gatsby";

    public static final int NUMBER_OF_NIGHTS = 5;

    /**
     * Sets the instance variable <tt>hotel</tt> to a well-defined initial value.
     * All test methods should be preceded by a call to this method.
     */
    @BeforeEach
    public void setUp() {
        hotel = new PricedHotel("Fawlty Towers");

        // initialisation of password-variable
        correctPassword = new Password().getInitPass();
        wrongPassword = correctPassword + "_invalid";
    }

    /**
     * checkIn First room should be a PricedRoom
     */
    @Test
    public void testCheckIn() {
        Room room = hotel.checkIn(GUEST_NAME_1);
        assertTrue(room instanceof PricedRoom,
                   "room should be an instance of PricedRoom");
        Safe safe = room.getSafe();
        assertTrue(safe instanceof PricedSafe,
                   "safe should be an instance of PricedSafe");
    }

    /**
     * If there is a free room, getFreeRoom must return a room without guest.
     */
    @Test
    public void testGetFreeRoomFromNotFullHotel() {
        Room room = hotel.getFreeRoom();
        assertNull(room.getGuest(), "A room is free");
        hotel.checkIn(GUEST_NAME_1);
        Room freeRoom = hotel.getFreeRoom();
        assertNotNull(freeRoom, "Another room is free");
        assertNotEquals(room, freeRoom, "Another room is free");
    }

    /**
     * If there is no free room, getFreeRoom must return null.
     */
    @Test
    public void testGetFreeRoomFromFullHotel() {
        hotel.checkIn(GUEST_NAME_1);
        hotel.checkIn(GUEST_NAME_2);

        Room noRoom = hotel.getFreeRoom();
        assertNull(noRoom, "No room available in a full hotel");
    }

    /**
     * getRoom must not return any room, if the guest is not checked in
     */
    @Test
    public void testGetRoomBeforeCheckIn() {
        Room room = hotel.getRoom(GUEST_NAME_1);
        assertNull(room, "Guest 1 not checked in");
    }

    /**
     * If the guest is checked in, the returned room must be occupied by the specified guest.
     */
    @Test
    public void testGetRoomAfterCheckIn() {
        hotel.checkIn(GUEST_NAME_1);
        Room room = hotel.getRoom(GUEST_NAME_1);
        assertEquals(GUEST_NAME_1, room.getGuest().getName(), "Guest 1 checked in");
    }

    /**
     * A password object must be returned.
     */
    @Test
    public void testGetPassword() {
        Room room = hotel.checkIn(GUEST_NAME_1);
        assertTrue(room instanceof PricedRoom,
                   "room should be an instance of PricedRoom");
        Safe safe = room.getSafe();
        assertTrue(safe instanceof PricedSafe,
                   "safe should be an instance of PricedSafe");

        Password password = ((PricedSafe) safe).getPassword();
        assertNotNull(password, "Returned password is not null");
    }

    /**
     * The Bill should be correctly calculated
     */
    @Test
    public void testGetBill() {
        Room room = hotel.checkIn(GUEST_NAME_1);
        this.correctPassword = ((PricedSafe) room.getSafe()).getPassword().getInitPass();
        assertInstanceOf(PricedRoom.class, room, "room should be an instance of PricedRoom");
        StringBillPrinter printer = new StringBillPrinter();
        Bill bill = hotel.getBill(GUEST_NAME_1, NUMBER_OF_NIGHTS, printer);
        double nightsTotal = NUMBER_OF_NIGHTS * PricedHotel.ROOM_PRICE;
        assertEquals(nightsTotal, bill.getSum(), 0.01, "Bill sum should contain only room costs.");
        assertTrue(printer.getResult().contains(String.format("%.2f", nightsTotal)));

        // Now check sum again when safe is actually active
        assertInstanceOf(PricedSafe.class, room.getSafe());
        PricedSafe safe = (PricedSafe) room.getSafe();
        assertFalse(safe.isActive(), "Safe should be deactivated after initialisation.");
        safe.activate(correctPassword);
        assertTrue(safe.isActive(), "Safe should be activated after activation with password.");
        Assertions.assertEquals(nightsTotal + PricedHotel.SAFE_PRICE,
                                hotel.getBill(GUEST_NAME_1, NUMBER_OF_NIGHTS, printer).getSum());
    }
}
