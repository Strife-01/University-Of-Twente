package ss.week4;

import java.util.ArrayList;
import java.util.List;

/**
 * Class takes in an iterable of type List and sorts it using divide and concur.
 * The mergesort method takes in every List type of comparable elements in order to sort them.
 * Don't forget to have the elements type of Comparable and in special cases Override the
 * compareTo(E o) method
 */
public class MergeSort {
    /*@
        requires data.getFirst() != null ==> data.getFirst() instanceof Comparable;
        ensures \result.size() >= 2 ==> (\forall int i; 0 <= i && i < \result.size() - 1;
        ((\result.get(i)).compareTo(\result.get(i + 1))) <= 0);
    */
    public static <E extends Comparable<E>> List<E> mergeSort(List<E> data) {
        if (data.size() >= 2) {
            // Get the mid-index of the data
            int midIndex = data.size() / 2;
            // Merge first half
            // if the mid-index is not seen then it goes to infinity - off by 1 error every fucking
            // God damned time
            List<E> firstHalf = mergeSort(data.subList(0, midIndex));
            // Merge second half
            List<E> secondHalf = mergeSort(data.subList(midIndex, data.size()));
            // The result of the current recursion step
            List<E> result = new ArrayList<>();
            // Comparing the elements in the 2 halves until one overflows the other
            int firstIndex = 0, secondIndex = 0;
            while (firstIndex < firstHalf.size() && secondIndex < secondHalf.size()) {
                if (firstHalf.get(firstIndex).compareTo(secondHalf.get(secondIndex)) <= 0) {
                    result.add(firstHalf.get(firstIndex));
                    firstIndex++;
                } else {
                    result.add(secondHalf.get(secondIndex));
                    secondIndex++;
                }
            }
            // Copy the remaining elements in the list
            while (firstIndex < firstHalf.size()) {
                result.add(firstHalf.get(firstIndex));
                firstIndex++;
            }
            while (secondIndex < secondHalf.size()) {
                result.add(secondHalf.get(secondIndex));
                secondIndex++;
            }
            // Return the current sort of sorted list
            return result;
        }
        // In case the data.size() == 1 or 0 return
        return data;
    }
}
