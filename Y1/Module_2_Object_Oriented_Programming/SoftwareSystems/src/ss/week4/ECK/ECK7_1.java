package ss.week4.ECK;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class ECK7_1 {
    List<Integer> list;

    public ECK7_1(int randomCap, int numberOfElements) {
        list = new ArrayList<>(numberOfElements);
        Random rand = new Random();
        for (int i = 0; i < numberOfElements; i++) {
            list.add(rand.nextInt(0, randomCap));
        }
    }

    public static void main(String[] args) {
        ECK7_1 object = new ECK7_1(1000000, 20);
        for (Integer i : object.list) {
            System.out.println(i);
        }
    }
}
