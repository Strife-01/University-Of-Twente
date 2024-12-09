package integrationTestData;

import java.util.ArrayList;
import java.util.List;
import java.io.EOFException;

/**
 * A room to store boxes in
 */
public class StorageSpace {

    /*@nullable*/private final List<Box> boxes = new ArrayList<>();

    // the total number of boxes that were shipped from this storage space, cannot be negative
    //@ <error descr="Modifier 'pure' is not allowed above a field">pure</error> (* pure is not allowed here. *)
    // pure <-- not a JML comment
    private int nrOfBoxesShipped = 0;
    // the total number of boxes in the storage space that are filled, cannot be negative
    protected int /*@
        (* whitespace *)
@spec_protected
        */ nrOfFullBoxes = 0 /*@<error descr="You cannot have multiple specification visibility modifiers (spec_public or spec_protected)">spec_public</error>*/ /* <weak_warning descr="To be considered a JML comment, there should be no whitespace between the start of the comment (/* or //) and the @-sign">@</weak_warning>spec_public (* more whitespace *)*/;

    //@ private invariant boxes != null;
    // invariant is static and boxes is not
    //@ private static invariant <error descr="A static invariant can only see static fields">boxes</error> != null;


    /*@@@@@@@
      @@@ private invariant nrOfBoxesShipped >= 0 && <error descr="The (specification) visibility of the reference should be the same as the visibility of the invariant">nrOfFullBoxes</error> >= 0;
      (* \elemtype needs an array and type class *)
      private invariant \elemtype(<error descr="This is not an array">boxes.getClass()</error>) instanceof Box;
      private invariant \elemtype(<error descr="This should be of type java.lang.Class, maybe you forgot to use .class or .getClass()?"><warning descr="JML expressions should be pure and this method might not be pure">boxes.toArray(new Box[0])</warning></error>) == \type(Box);
      private invariant \elemtype(<error descr="Not a valid expression">boxes.toArray(new Box[0]).class</error>) == \type(Box);
      private invariant \elemtype(<warning descr="JML expressions should be pure and this method might not be pure">boxes.toArray(new Box[0])</warning>.getClass()) instanceof \TYPE;
      private invariant \nonnullelements(boxes.toArray());
      @@@@@@@*/
    /*@ private invariant \elemtype(boxes.toArray(new Box[0]).getClass( == \type(Box)<error descr="Right parenthesis expected, got ';'">;</error>
      @ private invariant nrOfBoxesShipped >= 0;
    */

    // returns the weight of all the boxes together
    //@   ensures \result == (\sum int i; i >= 0 && i < boxes.size(); <warning descr="JML expressions should be pure and this method might not be pure">boxes.get(i).getWeight()</warning>);
    //@ pure
    public float getTotalWeight() {
        int currentWeight = 0;
        //@ loop_invariant <error descr="Reference cannot be resolved">box.getWeight</error> > 0;
        for (Box box : boxes) {
            currentWeight += box.getWeight();
        }
        return currentWeight;
    }

    // returns the average weight of the boxes, or 0 if there are no boxes
    //@ ensures <error descr="This must be of type boolean, but is float">\result == boxes.size() == 0 ? 0 : getTotalWeight() / <warning descr="JML expressions should be pure and this method might not be pure">getNrOfBoxes()</warning></error>; (* need parentheses around conditional expression *)
    // some syntactical errors
    //@ ensures \result == (boxes.size() == 0 ? 0 : getTotalWeight() / getNrOfBoxes()<error descr="Semicolon expected after this token">)</error>
    //@ <error descr="Class invariant, in-method specification, method specification, modifiers or at-sign expected, got 'esuress'">esuress</error> \result >= 0;
    //@ ensures <error descr="'\not_specified' or expression expected, got '\'">\</error>rsul >= 0;
    //@ requires \not_specified;
    // some semantic errors with exceptions
    /*@ <warning descr="Use a single signals_only clause to avoid confusion">signals_only ArithmeticException;</warning>
    signals (ArithmeticException)  nrOfFullBoxes == 0;
    signals (<error descr="This class could not be resolved, did you forget to import it?">IOException</error>) nrOfFullBoxes == 0;
    <warning descr="Use a single signals_only clause to avoid confusion">signals_only <error descr="This exception (or a superclass or subclass of it) should be mentioned in the throws clause of this method">EOFException</error>;</warning>
    signals (<error descr="This class could not be resolved, did you forget to import it?">AritheeemeticException</error> e) <error descr="Reference cannot be resolved">e</error> instanceof RuntimeException;
    */
    public float getAverageWeight() /*<error descr="Modifiers are not allowed before a method body">@pure</error>*/ {
        //@ assume boxes.size() >= 0;
        if (boxes.size() != 0) {
            return getTotalWeight() / getNrOfBoxes();
        }
        return 0;
    }

    // returns a list with boxes that have a volume >= the minimum volume specified
    /*@ (* requires after ensures in the same spec *)
      @ ensures (\forall int i; 0 <= i && i < boxes.size();
            boxes.get(i).getVolume() >= minimumVolume ==> \result.contains(boxes.get(i)));
      @ ensures \result.size() <= boxes.size();
      @ <error descr="Requires clauses must be placed before all other clauses in a specification as it is a pre-condition">requires</error> minimumVolume > 0;
    */
    //@ (* accessing variable declared inside method is not allowed *)
    //@ ensures <error descr="Reference cannot be resolved">goodBoxes</error>.size() >= 0;
    //@ pure;
    public List<Box> getAllBoxesWithMinVolume(float minimumVolume) {
        List<Box> goodBoxes = new ArrayList<>();

        //@ loop_invariant box.volume >= minimumVolume == goodBoxes.contains(box);
        for (Box box : boxes) {
            if (box.getVolume() >= minimumVolume) {
                goodBoxes.add(box);
            }
        }
        return goodBoxes;
    }

    // returns the heaviest box, or null if there are no boxes
    // mix of syntactical and type errors
    //@ requires <error descr="Not a valid expression">boxes != null && boxes.size) > 0</error>;
    //@ ensures (\forall int i; i > 0 && i < <error descr="Reference cannot be resolved">boxes.lenght</error>; <warning descr="JML expressions should be pure and this method might not be pure">boxes.get(i).getWeight()</warning> <= <error descr="Reference cannot be resolved">\result.weigh</error>);
    public Box getHeaviestBox() {
        if (getNrOfBoxes() != 0) {
            Box heaviest = boxes.get(0);
            //@maintaining <warning descr="JML expressions should be pure and this method might not be pure">boxes.get(i).getWeight()</warning> > 0;
            for (int i = 1; i < getNrOfBoxes(); i++) {
                Box current = boxes.get(i);
                if (current.getWeight() > heaviest.getWeight()) {
                    heaviest = current;
                }
            }
            //@ assert heaviest != null;
            return heaviest;
        }
        return null;
    }

    // removes the first x non-empty boxes from the storage space to ship them to somewhere else
    // maximumWeight: the maximum weight the entire shipment is allowed to be
    /*@

    ensures \result != null;
        ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
        ensures (\forall int i; 0 <= i && i < \result.size(); \old(boxes.contains(\result.get(i))));
        ensures (\forall int i; 0 <= i && i < \result.size(); !boxes.contains(\result.get(i)));
        ensures (\forall int i; i <= i && i < \result.size());
        (* comments inside a Java expr *)
        ensures (\forall int i; 0 <= i && i < \result.size(); <error descr="Not a valid expression">(* comment *) !boxes.contains(\result.get(i))</error>);
    */
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); <error descr="Not a valid expression">/* comment */ !boxes.contains(\result.get(i))</error>);
    public List<Box> createShipment(float maximumWeight) {
        List<Box> boxesForShipment = new ArrayList<>();
        float currentWeight = 0;
        int i = 0;
        while (nrOfFullBoxes > 0 && currentWeight + boxes.get(i).getWeight() < maximumWeight) {
            Box currentBox = boxes.get(0);
            if (currentBox.getItem() != null) {
                boxesForShipment.add(boxes.remove(0));
                nrOfFullBoxes--;
                //@ assert<error descr="Expression expected, got ';'">;</error>
                currentWeight += currentBox.getWeight();
            } else {
                i++;
                //@ assert \old(i) + 1 == i;
            }
        }
        nrOfBoxesShipped += boxesForShipment.size();
        return boxesForShipment;
    }

    // fills the first empty box which can fit the item
    // item: the item that goes in the box
    // returns true if a box could be filled
    /*@
      @ requires item != null;
      @ requires <warning descr="JML expressions should be pure and this method might not be pure">item.getVolume()</warning> > 0 && item.getWeight() > 0;
      @ ensures boxes.size() == 0 ==> \result == false;
      @ ensures (\exists int i;
           0 <= i && i < boxes.size();
           boxes.get(i).getItem() == null && boxes.get(i).getVolume() >= <warning descr="JML expressions should be pure and this method might not be pure">item.getVolume()</warning>
        ) <==> \old(nrOfFullBoxes) + 1 == nrOfFullBoxes && \result == true;
    */
    public boolean fillABox(Box.BoxItem item) {
        for (Box box : boxes) {
            if (box.getItem() == null && box.getVolume() >= item.getVolume()) {
                box.fill(item);
                nrOfFullBoxes++;
                return true;
            }
        }
        return false;
    }

    // add a box to the storage space
    //@ requires box != null;
    //@ ensures \old(boxes.size()) + 1 == boxes.size(<error descr="Semicolon expected after this token">)</error>
    public void addBox(Box box) /*@ ensures nrOfFullBoxes == \old(nrOfFullBoxes) + (box.getItem() != null ? 1 : 0);*/ {
        boxes.add(box);
        nrOfFullBoxes += box.getItem() != null ? 1 : 0;
    }


    // just some basic getters

    public int getNrOfBoxesShipped() {
        return nrOfBoxesShipped;
    }

    public int getNrOfFullBoxes() {
        return nrOfFullBoxes;
    }

    public List<Box> getBoxes() {
        //@ assert boxes != null;
        return boxes;
    }

    // <weak_warning descr="To be considered a JML comment, there should be no whitespace between the start of the comment (/* or //) and the @-sign">@</weak_warning>pure (* when calling this method, it should not be pure *)
    public int getNrOfBoxes() {
        return boxes.size();
    }
}
