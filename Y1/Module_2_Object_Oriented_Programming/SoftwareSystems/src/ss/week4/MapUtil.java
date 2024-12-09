package ss.week4;

import java.util.*;

public class MapUtil {
    /**
     * Checks if a give map is injective.
     * @param map map to be checked
     * @return true if the map is injective
     * @param <K> type parameter for key
     * @param <V> type parameter for value
     */
    /*@
        requires map != null;
        ensures (\forall K key1; map.containsKey(key1);
                  (\forall K key2; map.containsKey(key2) && !key1.equals(key2);
                      !map.get(key1).equals(map.get(key2))));
        ensures \result == (\forall K key1; map.containsKey(key1);
                            (\forall K key2; map.containsKey(key2) && !key1.equals(key2);
                                !map.get(key1).equals(map.get(key2))));
    @*/
    public static <K, V> boolean isOneOnOne(Map<K, V> map) {
        Set<K> mapKeys = map.keySet();
        int makKeySize = mapKeys.size();
        for (K key : mapKeys) {
            for (K checkKey : mapKeys) {
                if (!key.equals(checkKey) && map.get(key).equals(map.get(checkKey))) {
                    return false;
                }
            }
        }
        return true;
    }

    /*@
        requires map != null && range != null;
        ensures (\forall V value; range.contains(value);
               (\exists K key; map.containsKey(key); map.get(key).equals(value)))
            <==> \result;
    */
    public static <K, V> boolean isSurjectiveOnRange(Map<K, V> map, Set<V> range) {
        Set<V> testRange = new HashSet<>();
        for (K key : map.keySet()) {
            if (range.contains(map.get(key))) {
                testRange.add(map.get(key));
            }
        }
        return testRange.size() == range.size();
    }

    // The reason why we have a set of keys instead of individual keys is because
    // If the function is not bijective then there might
    // Be multiple keys that point to the same value so if we go in reverse then 1
    // Value has multiple keys but that by default nullifies the concept of a
    // mathematical map
    /*@
        requires map != null;
        ensures \result != null;
        ensures (\forall K key; map.containsKey(key);
               (\exists V value; map.get(key).equals(value) &&
                   \result.containsKey(value) &&
                   \result.get(value) != null &&
                   \result.get(value).contains(key)));
        ensures (\forall V value; \result.containsKey(value);
               (\forall K key; \result.get(value).contains(key);
                   map.get(key).equals(value)));
    */
    public static <K, V> Map<V, Set<K>> inverse(Map<K, V> map) {
        // TODO: implement
        Set<K> keys;
        Map<V, Set<K>> inverse = new HashMap<>();
        for (K key : map.keySet()) {
            V value = map.get(key);
            if (inverse.get(value) == null) {
                keys = new HashSet<>();
                keys.add(key);
                inverse.put(value, keys);
            } else {
                inverse.get(value).add(key);
            }
        }
        return inverse;
    }

    /*@
        requires map != null;
        requires (\forall K key1; map.containsKey(key1);
                    (\forall K key2; map.containsKey(key2) && !key1.equals(key2);
                        !map.get(key1).equals(map.get(key2))));
        requires (\forall V value; map.values().contains(value);
                    (\exists K key; map.containsKey(key); map.get(key).equals(value)));
        ensures (\result == null) <==> !(isOneOnOne(map) && isSurjectiveOnRange(map, Set.copyOf(map.values())));
        ensures (\result != null) ==>
                 (\forall V value; \result.containsKey(value);
                     map.get(\result.get(value)).equals(value)) &&
                 (\forall K key; map.containsKey(key);
                     \result.containsKey(map.get(key)) && \result.get(map.get(key)).equals(key));
    */
    public static <K, V> Map<V, K> inverseBijection(Map<K, V> map) {
        Set<K> keys = map.keySet();
        Set<V> values = Set.copyOf(map.values());
        Map<V, K> bijection;
        if (!(isOneOnOne(map) && isSurjectiveOnRange(map, values))) {
            return null;
        }
        bijection = new HashMap<>();
        for (K key : keys) {
            bijection.put(map.get(key), key);
        }
        return bijection;
    }

    /*@
        requires f != null && g != null;
        ensures \result == (\forall K key; f.containsKey(key);
                           g.containsKey(f.get(key)));
    */
    public static <K, V, W> boolean compatible(Map<K, V> f, Map<V, W> g) {
        for (K key : f.keySet()) {
            if (g.get(f.get(key)) == null) {
                return false;
            }
        }
        return true;
    }

    /*@
        requires f != null && g != null;
        ensures (\result == null) <==> !compatible(f, g);
        ensures \result != null ==>
             (\forall K key; f.containsKey(key);
                 \result.get(key).equals(g.get(f.get(key))));
    */
    public static <K, V, W> Map<K, W> compose(Map<K, V> f, Map<V, W> g) {
        if (!compatible(f, g)) {
            return null;
        }
        Map<K, W> composed = new HashMap<>();
        for (K key : f.keySet()) {
            composed.put(key, g.get(f.get(key)));
        }
        return composed;
    }
}
