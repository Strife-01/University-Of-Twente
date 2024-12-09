package ss.hotel.bill;

public class SysoutBillPrinter implements BillPrinter {
    /**
     * First formats the text and them prints it to the standard output.
     * @param text item
     * @param price price of item
     */
    /*@
        requires text instanceof String && text != "";
        requires price instanceof double && price >= 0;
        pure
    */
    @Override
    public void printLine(String text, double price) {
        System.out.print(format(text, price));
    }

    public static void main(String[] args) {
        SysoutBillPrinter p = new SysoutBillPrinter();
        p.printLine("Text1", 1.0);
        p.printLine("Other␣text", -12.1212);
        p.printLine("Something", .2);
    }
}
