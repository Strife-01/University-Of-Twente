package ss.week4;

import java.util.*;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;


public class MergeSortTest {
    @Test
    public void testMergesortEmptyList() {
        List<Integer> sequence = new ArrayList<>(Collections.emptyList());
        List<Integer> result = MergeSort.mergeSort(sequence);
        assertEquals(Collections.emptyList(), result);
    }

    @Test
    public void testMergesortSingleItem() {
        List<Integer> sequence = new ArrayList<>(Arrays.asList(1));
        List<Integer> result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1), result);
    }

    @Test
    public void testMergesortSortedList() {
        List<Integer> sequence = new ArrayList<>(Arrays.asList(1, 2, 3, 4, 5));
        List<Integer> result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1, 2, 3, 4, 5), result);

        sequence = new ArrayList<>(Arrays.asList(1, 2, 3, 4, 5, 6));
        result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1, 2, 3, 4, 5, 6), result);
    }

    @Test
    public void testMergesortUnsortedList() {
        List<Integer> sequence = new ArrayList<>(Arrays.asList(3, 2, 1, 5, 4));
        List<Integer> result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1, 2, 3, 4, 5), result);

        sequence = new ArrayList<>(Arrays.asList(3, 2, 1, 6, 5, 4));
        result = MergeSort.mergeSort(sequence);
        assertEquals(Arrays.asList(1, 2, 3, 4, 5, 6), result);
    }

    @Test
    public void test20000RandomIntegers() {
        List<Integer> sequence = new ArrayList<>();
        int numberOfIntegers = 20000;
        int maxNumber = 1000000000;
        Random rand = new Random();
        for (int i = 0; i < numberOfIntegers; i++) {
            sequence.add(rand.nextInt(maxNumber));
        }
        sequence.sort(Integer::compareTo);
        List<Integer> result = MergeSort.mergeSort(sequence);
        assertEquals(sequence, result);
    }
}