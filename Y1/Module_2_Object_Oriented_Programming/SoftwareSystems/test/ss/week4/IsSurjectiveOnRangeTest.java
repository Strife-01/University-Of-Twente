package ss.week4;

import org.junit.jupiter.api.Test;


import ss.week4.MapUtil;

import java.util.*;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class IsSurjectiveOnRangeTest {
    private Map<Integer, Character> f1;
    private Set<Character> range;

    @Test
    public <K, V> void testEmptyMap() {
        f1 = new HashMap<Integer, Character>();
        range = new HashSet<Character>();

        assertTrue(MapUtil.isSurjectiveOnRange(f1, range));
    }

    @Test
    public <K, V> void testCorrectMaps() {
        f1 = new HashMap<Integer, Character>();
        f1.put(1, 'a');
        f1.put(2, 'b');

        range = new HashSet<Character>(Arrays.asList('a', 'b'));

        assertTrue(MapUtil.isSurjectiveOnRange(f1, range));

        f1 = new HashMap<Integer, Character>();
        f1.put(1, 'a');
        f1.put(2, 'b');
        f1.put(3, 'a');

        range = new HashSet<Character>(Arrays.asList('a', 'b'));

        assertTrue(MapUtil.isSurjectiveOnRange(f1, range));
    }

    @Test
    public void testWrongMaps() {
        f1 = new HashMap<Integer, Character>();
        f1.put(1, 'b');
        f1.put(2, 'b');

        range = new HashSet<Character>(Arrays.asList('a', 'b'));

        assertFalse(MapUtil.isSurjectiveOnRange(f1, range));

        f1 = new HashMap<Integer, Character>();
        f1.put(1, 'b');
        f1.put(2, 'c');

        range = new HashSet<Character>(Arrays.asList('a', 'b'));

        assertFalse(MapUtil.isSurjectiveOnRange(f1, range));
    }

}
