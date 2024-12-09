package ss.week4;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import ss.week4.DoublyLinkedList;

public class DoublyLinkedListTest {
    private DoublyLinkedList<Object> list;
    private Object object1;
    private Object object2;
    private Object object3;
    private Object object4;

    @BeforeEach
    public void setUp() {
        list = new DoublyLinkedList<>();
        object1 = new Object();
        object2 = new Object();
        object3 = new Object();
        object4 = new Object();
    }

    @Test
    public void testSetup() {
        assertEquals(0, list.size());
    }

    @Test
    public void testAdd() {
        list.add(0, object1); // Test adding
        list.add(0, object2); // Test adding at the start
        assertEquals(2, list.size());
        assertEquals(object1,list.get(1));
        assertEquals(object2, list.get(0));
        list.add(2, object3); // Test adding at the end
        list.add(1, object4); // Test adding in the middle
        assertEquals(4, list.size());
        assertEquals(object4, list.get(1));
        assertEquals(object1, list.get(2));
        assertEquals(object3, list.get(3));
    }

    @Test
    public void testRemoveHead() {
        list.add(0, object1);
        list.add(1, object2);
        list.add(2, object3);

        list.remove(0);
        assertEquals(object2, list.get(0));
        assertEquals(2, list.size());
    }

    @Test
    public void testRemove() {
        list.add(0, object1);
        list.add(1, object2);
        list.add(2, object3);

        list.remove(1);
        assertEquals(object3, list.get(1));
        assertEquals(2, list.size());
    }
}
