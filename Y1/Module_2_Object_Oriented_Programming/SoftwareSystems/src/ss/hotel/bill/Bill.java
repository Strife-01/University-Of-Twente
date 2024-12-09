package ss.hotel.bill;

/**
 * Bill having multiple items. Lab assignment Module 2
 */
public class Bill {
    protected BillPrinter billPrinter;
    protected double totalPrice = 0.0;

    /*@
        protected invariant billPrinter instanceof BillPrinter;
        protected invariant totalPrice >= 0.0;
    */

    /**
     * Abstraction of the items on the bill.
     * Every item has a price and description; the description is available with toString().
     */
    public static interface Item {
        String description = "";
        double price = 0.0;

        /*@
            public invariant description != null;
            public invariant price >= 0.0;
        */

        /**
         * Returns the price of this Item.
         * @return the price of this Item.
         */
        /*@
            ensures \result >= 0.0;
            pure
        */
        double getPrice();

        /**
         * The user is obligated to override toString to get the description of the item.
         * @return the description of the item
         */
        /*@
            ensures \result != null;
            pure
        */
        @Override
        public String toString();
    }

    public class Nights implements Item {
        private int nights;
        private double price;
        private String description;

        public Nights(int nights, double pricePerNight) {
            this.nights = nights;
            this.price = pricePerNight;
            this.description = "The guest staid ";
        }

        /**
         * Returns the price of this Item.
         * @return the price of this Item.
         */
        @Override
        public double getPrice() {
            return this.price;
        }

        public int getNights() {
            return nights;
        }

        public void setNights(int nights) {
            this.nights = nights;
        }

        @Override
        public String toString() {
            return this.description + this.nights + ".";
        }
    }

    /**
     * Constructs a Bill sending the output to a given Printer.
     * @param billPrinter the printer to send the bill to
     */
    /*@
        requires billPrinter instanceof BillPrinter;
        requires billPrinter != null;
        ensures billPrinter != null ==> this.billPrinter != null;
    */
    public Bill(BillPrinter billPrinter) {
        this.billPrinter = billPrinter;
    }

    /**
     * Adds an item to this Bill.
     * The item is sent to the printer, and the price is added to the sum of the Bill
     * @param item the new item
     */
    /*@
        requires item != null;
        requires item instanceof Item;
        ensures item != null ==> totalPrice == totalPrice + item.getPrice();
    */
    public void addItem(Item item) {
        billPrinter.printLine(item.toString(), item.getPrice());
        this.totalPrice += item.getPrice();
    }

    /**
     * Sends the sum total of the bill to the printer.
     */
    public void close() {
        billPrinter.printLine("Total", getSum());
    }

    /**
     * Returns the current sum total of the Bill.
     * @return current sum of total Bill.
     */
    /*@
        ensures \result == this.totalPrice;
        pure
    */
    public double getSum() {
        return this.totalPrice;
    }

    /**
     * For test only.
     */
    public BillPrinter getBillPrinter() {
        return this.billPrinter;
    }
}
