package ss.week4;

import java.util.ArrayList;
import java.util.List;

public class CorrectUtil<T> {
    public static <T> List<T> zip(List<T> l1, List<T> l2) {
        ArrayList<T> result = new ArrayList<>();
        int minSize = Math.min(l1.size(), l2.size());
        int maxSize = Math.max(l1.size(), l2.size());
        List<T> overflowingList = maxSize == l1.size() ? l1 : l2;
        int i;
        for (i = 0; i < minSize; i++) {
            result.add(l1.get(i));
            result.add(l2.get(i));
        }
        for (int j = i; j < maxSize; j++) {
            result.add(overflowingList.get(j));
        }
        return result;
    }

    /**
     * signNumber function checks for the sign of the integer provided as argument.
     * @param number number to check the sign of
     * @return -1, 0 or 1 if the argument is negative, 0 or positive
     */
    public static int signNumber(int number) {
        // Boring way
        if (number < 0) {
            return -1;
        } else if (number > 0) {
            return 1;
        }
        return 0;
        // Another more hipster way
        // return Integer.compare(number, 0);
        // return number < 0 ? -1 : number > 0 ? 1 : 0;
    }
}
