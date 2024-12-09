package ss.week2.hotel.items;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ss.hotel.PricedSafe;
import ss.hotel.bill.Bill;

public class PricedSafeTest {

    private PricedSafe safe;
    private static final double PRICE = 6.36;
    private static final String PRICE_PATTERN = ".*6[.,]36.*";
    private static final String DESCRIPTION = "The price for this safe is " + PRICE + ".";

    public String CORRECT_PASSWORD;
    public String WRONG_PASSWORD;


    @BeforeEach
    public void setUp() throws Exception {
        safe = new PricedSafe(PRICE);
        CORRECT_PASSWORD = safe.getPassword().getInitPass();
        WRONG_PASSWORD = CORRECT_PASSWORD + "WRONG";
        assertFalse(safe.isActive());
        assertFalse(safe.isOpen());
    }

    @Test
    public void testIsBillItem() throws Exception {
        assertTrue(safe instanceof Bill.Item,
                   "safe should be an instance of Bill.Item.");
        assertEquals(PRICE, safe.getPrice(), 0,
                     "GetPrice should return the price of the safe.");
    }

    @Test
    public void testGetPrice() {
        assertEquals(PRICE, safe.getPrice());
    }

    @Test
    public void testToString() {
        assertEquals(DESCRIPTION, safe.toString());
    }

    @Test
    public void testDeactivatedWithCorrectPassword() {
        safe.activate(CORRECT_PASSWORD);
        assertEquals(true, safe.isActive());
        assertEquals(false, safe.isOpen());
    }

    @Test
    public void testDeactivatedWithWrongPassword() {
        try {
            safe.activate(WRONG_PASSWORD);
        } catch (AssertionError _) {
        }
        assertEquals(false, safe.isActive());
        assertEquals(false, safe.isOpen());
    }

    @Test
    public void testOpenDeactivated() {
        try {
            safe.open(CORRECT_PASSWORD);
        } catch (AssertionError _) {
        }
        assertEquals(false, safe.isActive());
        assertEquals(false, safe.isOpen());
    }

    @Test
    public void testOpenDeactivatedWrong() {
        try {
            safe.open(WRONG_PASSWORD);
        } catch (AssertionError _) {
        }
        assertEquals(false, safe.isActive());
        assertEquals(false, safe.isOpen());
    }

    @Test
    public void testActivateAndOpen() {
        try {
            safe.activate(CORRECT_PASSWORD);
            safe.open(WRONG_PASSWORD);
        } catch (AssertionError _) {
        }
        assertEquals(true, safe.isActive());
        assertEquals(false, safe.isOpen());

        try {
            safe.open(CORRECT_PASSWORD);
        } catch (AssertionError _) {
        }
        assertEquals(true, safe.isActive());
        assertEquals(true, safe.isOpen());
    }

    @Test
    public void testActivateAndOpenClose() {
        try {
            safe.activate(CORRECT_PASSWORD);
            safe.open(CORRECT_PASSWORD);
            safe.close();
        } catch (AssertionError _) {
        }
        assertEquals(true, safe.isActive());
        assertEquals(false, safe.isOpen());
    }

    @Test
    public void testCloseDeactivated() {
        safe.close();
        assertEquals(false, safe.isActive());
        assertEquals(false, safe.isOpen());
    }
}
