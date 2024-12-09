package ss.hotel;

import ss.hotel.bill.Bill;
import ss.hotel.password.Password;

public class PricedRoom extends Room implements Bill.Item {
    private double price;
    private double safePrice;
    public PricedRoom(int number, double roomPrice, double safePrice) {
        super(number, new PricedSafe(safePrice));
        this.price = roomPrice;
        this.safePrice = safePrice;
    }

    public PricedRoom(int number, double roomPrice, double safePrice, Password password) {
        super(number, new PricedSafe(safePrice, password));
        this.price = roomPrice;
        this.safePrice = safePrice;
    }

    /**
     * Returns the price of this Item.
     * @return the price of this Item.
     */
    @Override
    public double getPrice() {
        return this.price;
    }

    @Override
    public String toString() {
        return "The price per night is " + (this.price + safePrice);
    }
}
