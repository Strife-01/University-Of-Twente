package integrationTestData;

/**
 * A storage box that can hold an item, it has a certain volume and weight
 */
public class Box {
    // should not be zero or negative
    //@ <error descr="Class invariant, in-method specification, method specification, modifiers or at-sign expected, got 'volume'">volume</error> > 0
    //@ spec_public
    private final float volume;
    // is the weight of the box itself plus the weight of the item in it, should not be zero or negative

    //<error descr="Class invariants are not allowed above a field, add a newline after the comment">@ public invariant weight > 0;</error>
    /*@ spec_public */private float weight;

    //@ <error descr="Modifier 'pure' is not allowed before a class_invariant">pure</error> public invariant weight > 0;
    //@ private invariant item == null ? true : <warning descr="JML expressions should be pure and this method might not be pure">item.getVolume()</warning> > 0 && item.getWeight() > 0;

    private BoxItem item = null;

    // weight is here the weight of the box when it is empty
    //@ requires weight > 0 && volume > 0;
    public Box(float weight, float volume) {
        this.weight = weight;
        this.volume = volume;
    }

    // fills the box with an item, the box needs to be empty for this
    /*@
        pre item != null && item.getWeight() > 0 && <warning descr="JML expressions should be pure and this method might not be pure">item.getVolume()</warning> > 0;
        also requires this.getItem() == null;
        post this.item == item;
        ensures this.weight == \old(this.weight) + item.getWeight();
        assignable this.item, this.weight, <error descr="This variable is final, so cannot be assigned">this.volume</error>;
        modifiable \everything;
        modifiable \nothing;
    */
    public void fill(BoxItem item) {
        //@ assert item != null;
        this.item = item;
        this.weight += item.getWeight();
    }

    //@ pure
    public float getVolume() {
        return volume;
    }


    // just some basic getters
    public float getWeight() {
        return weight;
    }

    //@ pure
    public Object getItem() {
        return item;
    }


    protected class BoxItem {
        private final Object item;
        private final float weight;
        private final float volume;

        //@ ensures \typeof(item) == \type(Object);
        protected BoxItem(Object item, float weight, float volume) {
            this.item = item;
            this.weight = weight;
            this.volume = volume;
        }

        //@ pure
        public float getWeight() {
            return weight;
        }

        public float getVolume() {
            return volume;
        }
    }


}
