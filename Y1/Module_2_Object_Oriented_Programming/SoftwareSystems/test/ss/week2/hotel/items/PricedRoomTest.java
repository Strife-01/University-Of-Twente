package ss.week2.hotel.items;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ss.hotel.PricedRoom;
import ss.hotel.bill.Bill;

public class PricedRoomTest {
    private Bill.Item item;
    private static final double PRICE = 6.36;
    private static final String PRICE_PATTERN = ".*6[.,]36.*";

    @BeforeEach
    public void setUp() throws Exception {
        item = new PricedRoom(0, PRICE, 0);
    }

    @Test
    public void testGetPrice() throws Exception {
        assertEquals(PRICE, item.getPrice(), 0,
                     "GetPrice should return the price of the room.");
    }

    @Test
    public void testToString() throws Exception {
        assertTrue(item.toString().matches(PRICE_PATTERN),
                   "The price per night should be included.");
    }
}
