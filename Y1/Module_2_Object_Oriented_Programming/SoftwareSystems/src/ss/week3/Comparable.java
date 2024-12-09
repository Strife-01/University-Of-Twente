package ss.week3;

public interface Comparable {
    /**
     * Checks whether this object is greater than the other.
     *
     * @requires this. isComparableTo (other)
     * @param other object to the compared
     * @return true if this is greater than other
     */
    public boolean greaterThan(Comparable other);

    /**
     * Checks whether this object can be compared to the other.
     *
     * @requires other != null
     *
     * @param other object ot be compared
     * @return true if objects can be compared
     */
    public boolean isComparableTo(Comparable other);
}
