package ss.hotel;

import ss.hotel.bill.Bill;
import ss.hotel.password.Password;

public class PricedSafe extends Safe implements Bill.Item {
    private double price;
    private Password password;

    public PricedSafe(double price) {
        super();
        this.price = price;
        this.password = new Password();
    }

    public PricedSafe(double price, Password password) {
        this(price);
        this.password = password;
    }

    public void activate(String passToCheck) {
        assert this.password.testWord(passToCheck) : "Wrong pass";
        if (this.password.testWord(passToCheck)) {
            super.activate();
        }
    }

    @Override
    public void activate() {
        System.out.println("Sorry you need a password to activate this safe.");
    }

    @Override
    public void deactivate() {
        super.deactivate();
    }

    public void open(String pass) {
        assert super.isActive() : "The safe needs to be activated to be opened";
        assert this.password.testWord(pass) : "Wrong pass";
        if (super.isActive() && this.password.testWord(pass)) {
            super.open();
        }
    }

    @Override
    public void open() {
        System.out.println("Sorry, you need a password to open this safe");
    }

    @Override
    public void close() {
        super.close();
    }

    public Password getPassword() {
        return this.password;
    }

    /**
     * Returns the price of this Item.
     *
     * @return the price of this Item.
     */
    @Override
    public double getPrice() {
        return this.price;
    }

    @Override
    public String toString() {
        return "The price for this safe is " + price + ".";
    }

    public static void main(String[] args) {
        PricedSafe safe = new PricedSafe(1);
        System.out.println(safe.password.getInitPass());
        safe.activate("Wrong");
    }
}
