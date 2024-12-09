package ss.hotel.bill;

public class StringBillPrinter implements BillPrinter {
    private String result = "";

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
        this.result += format(text, price);
}

    public String getResult() {
        String copy = this.result;
        this.result = "";
        return copy;
    }

    public static void main(String[] args) {
        StringBillPrinter p = new StringBillPrinter();
        p.printLine("Text1", 1.0);
        p.printLine("Other␣text", -12.1212);
        p.printLine("Something", .2);

        System.out.println(p.getResult());
        System.out.println(p.getResult());
    }
}
