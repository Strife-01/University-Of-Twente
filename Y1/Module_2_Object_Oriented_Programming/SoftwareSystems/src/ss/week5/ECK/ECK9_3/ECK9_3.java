package ss.week5.ECK.ECK9_3;

import java.util.LinkedList;
import java.util.List;

public class ECK9_3 {
    private List<Integer> ints;
    //List<Integer> revInts;

    class ListNode {
        int item; // An item in the list.
        ListNode next; // Pointer to the next node in the list.
    }

    public ECK9_3() {
        ints = new LinkedList<>();
    }

    public void populateList() {
        for (int i = 0; i < 100; i++) {
            ints.add(i);
        }
    }

    public List<Integer> returnRevesed() {
        return ints.reversed();
    }

    public static void main(String[] args) {
        ECK9_3 obj = new ECK9_3();
        obj.populateList();
        for (Integer i : obj.returnRevesed()) {
            System.out.println(i);
        }
    }
}
