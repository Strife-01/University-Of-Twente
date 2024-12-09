package ss.week2.hotel.bill;

import org.junit.jupiter.api.*;
import static org.junit.jupiter.api.Assertions.*;
import ss.hotel.bill.Bill;
import ss.hotel.bill.StringBillPrinter;
import ss.hotel.bill.SysoutBillPrinter;

public class BillTest {
    Bill bill1, bill2;
    Bill.Item[] items;
    StringBillPrinter billPrinter1;

    class TestItem implements Bill.Item {
        public final String description;
        public final double price;

        TestItem(String testDescription, double testPrice) {
            this.description = testDescription;
            this.price = testPrice;
        }

        @Override
        public double getPrice() {
            return this.price;
        }

        @Override
        public String toString() {
            return this.description;
        }
    }

    @BeforeEach
    public void init() {
        billPrinter1 = new StringBillPrinter();
        bill1 = new Bill(billPrinter1);
        bill2 = new Bill(new SysoutBillPrinter());

        items = new Bill.Item[3];
        TestItem item1 = new TestItem("Text1", 0);
        TestItem item2 = new TestItem("Other␣text", 0.1);
        TestItem item3 = new TestItem("Something", .2);
        items[0] = item1;
        items[1] = item2;
        items[2] = item3;
    }

    @Test
    public void testInitialState() {
        assertEquals(0.0, bill1.getSum());
        assertEquals(0.0, bill2.getSum());
    }

    @Test
    public void testInsertion() {
        String testOutput = "";
        for (Bill.Item item : items) {
            bill1.addItem(item);
            testOutput += billPrinter1.format(item.toString(), item.getPrice());

        }
        assertEquals(testOutput, billPrinter1.getResult());
        assertEquals(0.3, bill1.getSum(), 0.00001);
    }

    @Test
    public void testClosing() {
        String testOutput = "";
        for (Bill.Item item : items) {
            bill1.addItem(item);
            testOutput += billPrinter1.format(item.toString(), item.getPrice());

        }
        bill1.close();
        testOutput += billPrinter1.format("Total", 0.3);
        assertEquals(testOutput, billPrinter1.getResult());
    }
}
