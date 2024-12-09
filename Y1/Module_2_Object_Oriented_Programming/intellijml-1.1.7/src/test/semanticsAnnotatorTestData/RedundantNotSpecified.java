package semanticsAnnotatorTestData;

public class RedundantNotSpecified {
    private int x = 10;

    /*@
        requires b != 0;
        <warning descr="This clause containing \not_specified is redundant because you already specified it">requires \not_specified;</warning>
    */
    public int div(int a, int b) {
        return a / b;
    }

    /*@
         <warning descr="This clause containing \not_specified is redundant because you already specified it">ensures \not_specified;</warning>
         ensures b != 0;

    */
    public int div2(int a, int b) {
        return a / b;
    }

    /*@
         <warning descr="This clause containing \not_specified is redundant because you already specified it">modifiable \not_specified;</warning>
         modifies x;
         <warning descr="This clause containing \not_specified is redundant because you already specified it">assignable \not_specified;</warning>

    */
    public int div3(int a, int b) {
        return a / b;
    }

    /*@
         <warning descr="This clause containing \not_specified is redundant because you already specified it">requires \not_specified;</warning>
         <warning descr="This clause containing \not_specified is redundant because you already specified it">requires \not_specified;</warning>
    */
    public int div4(int a, int b) {
        return a / b;
    }

    /*@
        requires \not_specified;
        ensures \not_specified;
   */
    public int div5(int a, int b) {
        return a / b;
    }

    /*@
        <warning descr="This clause containing \not_specified is redundant because you already specified it">requires \not_specified;</warning>
    */
    public int div6(int a, int b) /*@ <warning descr="This clause containing \not_specified is redundant because you already specified it">requires \not_specified;</warning>
     */ {
        return a / b;
    }
}
