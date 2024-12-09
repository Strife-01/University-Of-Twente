package ss.week6;

import java.util.ArrayList;
import java.util.Collection;

public class ListAdder implements Runnable {
    private final Collection<Integer> numbers;
    private final int from;
    private final int to;

    public ListAdder(Collection<Integer> collection, int from, int to) {
        this.numbers = collection;
        this.from = from;
        this.to = to;
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        for (int i = from; i < to; i++) {
            addNumber(i);
        }
    }

    public void addNumber(int number) {
        numbers.add(number);
    }

    /**
     * Test the ListAdder class.
     * @param args command line arguments, not used
     */
    public static void main(String[] args) {
        Collection<Integer> numbers = new ArrayList<>();
        Thread thread1 = new Thread(new ListAdder(numbers, 0, 50000));
        Thread thread2 = new Thread(new ListAdder(numbers, 50000, 100000));
        try {
            thread1.start();
            thread2.start();
            thread1.join();
            thread2.join();
        } catch (InterruptedException e) {
        }
        System.out.println(numbers.size());
    }
}
