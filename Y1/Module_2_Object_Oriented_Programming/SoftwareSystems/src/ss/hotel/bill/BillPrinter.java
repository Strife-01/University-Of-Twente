package ss.hotel.bill;

import java.util.Formatter;

/**
 * Creates a printer for bills.
 */
public interface BillPrinter {
    /**
     * Takes in the item and the price and returns a string formated for a bill.
     * @param text the item
     * @param price the price
     * @return formatted text containing item on the left and price on the right
     */
    /*@
        requires text instanceof String && text != "";
        requires price instanceof double && price >= 0;
        ensures \result instanceof String;
        pure
    */
    default String format(String text, double price) {
        Formatter formatter = new Formatter();
        String s = "%-15s%10.2f\n";
        formatter.format(s, text, price);
        String returnString = formatter.toString();
        formatter.close();
        return returnString;
    }

    /**
     * First formats the text and them prints it.
     * @param text item
     * @param price price of item
     */
    /*@
        requires text instanceof String && text != "";
        requires price instanceof double && price >= 0;
        pure
    */
    void printLine(String text, double price);
}
