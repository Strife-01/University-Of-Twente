package ss.week3;

public class Date implements Comparable {

    private int day;
    private int month;
    private int year;

    Date(int year, int month, int day) {
        if (month > 12 || month < 1) {
            throw new IncompatibleType("There are only 12 months in a year.");
        }

        switch (month) {
            case 1, 3, 5, 7, 8, 10, 12:
                if (day < 1 || day > 31) {
                    throw new IncompatibleType("There are days from 1 to 31 in this month");
                }
                break;
            case 4, 6, 9, 11:
                if (day < 1 || day > 30) {
                    throw new IncompatibleType("There are days from 1 to 30 in this month");
                }
                break;
            default:
                if (day < 1 || day > 29) {
                    throw new IncompatibleType("There are days from 1 to 29 in this month");
                }
                break;
        }

        this.day = day;
        this.month = month;
        this.year = year;
    }

    /**
     * Checks whether this object is greater than the other.
     *
     * @param other object to the compared
     * @return true if this is greater than other
     * @requires this. isComparableTo (other)
     */
    @Override
    public boolean greaterThan(Comparable other) {
        if (!isComparableTo(other)) {
            throw new IncompatibleType("Types are not compatible!");
        }
        if (this.year < ((Date) other).year) {
            return false;
        } else if (this.year > ((Date) other).year) {
            return true;
        } else {
            if (this.month < ((Date) other).month) {
                return false;
            } else if (this.month > ((Date) other).month) {
                return true;
            } else {
                if (this.day <= ((Date) other).day) {
                    return false;
                }
                return false;
            }
        }
    }

    /**
     * Checks whether this object can be compared to the other.
     *
     * @param other object ot be compared
     * @return true if objects can be compared
     * @requires other != null
     */
    @Override
    public boolean isComparableTo(Comparable other) {
        return other instanceof Date;
    }

    public int getDay() {
        return this.day;
    }

    public int getMonth() {
        return this.month;
    }

    public int getYear() {
        return this.year;
    }
}
