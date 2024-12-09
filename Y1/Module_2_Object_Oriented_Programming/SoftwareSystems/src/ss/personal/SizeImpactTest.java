package ss.personal;

import java.util.ArrayList;
import java.util.List;

public class SizeImpactTest {
    public static void main(String[] args) {
        int size = 10000000;
        List<Integer> ints = new ArrayList<>(size);
        for (int i = 0; i < size; i++) {
            ints.add(i);
        }
        long startTime = System.nanoTime();
        for (int i = 0; i < ints.size(); i++) {
            //System.out.println(ints.get(i));
        }
        long stopTime = System.nanoTime();
        System.out.printf("It took %d nanoseconds for the .size() loop to complete\n", stopTime - startTime);

        startTime = System.nanoTime();
        for (int i = 0, s = ints.size(); i < s; i++) {
            //System.out.println(ints.get(i));
        }
        stopTime = System.nanoTime();
        System.out.printf("It took %d nanoseconds for the size loop to complete\n", stopTime - startTime);

    }
}
