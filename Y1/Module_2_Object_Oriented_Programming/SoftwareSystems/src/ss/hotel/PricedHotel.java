package ss.hotel;

import ss.hotel.bill.Bill;
import ss.hotel.bill.BillPrinter;

public class PricedHotel extends Hotel {
    public static final double ROOM_PRICE = 100;
    public static final double SAFE_PRICE = 12.5;

    /**
     * Creates a hotel object.
     * @param name the name of the hotel
     */
    public PricedHotel(String name) {
        super(name);
        super.rooms[0] = new PricedRoom(0, ROOM_PRICE, SAFE_PRICE);
    }

    public Bill getBill(String guestName, int numberNights, BillPrinter p) {
        if (super.getRoom(guestName) == null) {
            return null;
        } else if (!(super.getRoom(guestName) instanceof PricedRoom)) {
            return null;
        }
        Bill bill = new Bill(p);

        if (!super.getRoom(guestName).getSafe().isActive()){
            addDaysToBill(numberNights, bill);
        } else {
            addDaysToBill(numberNights, bill);
            Bill.Item s = new Bill.Item() {
                @Override
                public double getPrice() {
                    return SAFE_PRICE;
                }

                @Override
                public String toString() {
                    return "Safe Price";
                }
            };
            bill.addItem(s);
        }
        bill.close();
        return bill;
    }

    private void addDaysToBill(int numberNights, Bill bill) {
        for (int i = 0; i < numberNights; i++) {
            int finalI = i;
            Bill.Item day = new Bill.Item() {
                @Override
                public double getPrice() {
                    return ROOM_PRICE;
                }

                @Override
                public String toString() {
                    return "Day " + finalI;
                }
            };
            bill.addItem(day);
        }
    }
}
