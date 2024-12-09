package ss.week4;

import java.util.ArrayList;
import java.util.List;
// Problem 1 - Unused import - reason for problem - hogs memory for no reason
import java.lang.String;

// Problem 3 - Class uses generics but the class itself is not a generic
public class Util {
    // Problem 2 - Generic name should have 1 letter not multiple
    public static <Element> List<Element> zip
    // Problem 4 - Incorrect layout and whitespaces
            (List<Element> l1, List<Element> l2) {
        // Problem 5 - Capitalized non constant variable
        ArrayList<Element> RESULT = new ArrayList<>();
        // Problem 6 - The list will not contain all the elements from both lists
        // because the l1.size() and l2.size() can return different numbers
        // also there is a huge probability for IndexOutOfBoundsException as if
        // l2.size() returns a number less than l1.size() we will try to retrieve
        // an element from an index which is not present in the l2 list.
        for (int i = 0; i < l1.size(); i++) {
            RESULT.add(l1.get(i));
            RESULT.add(l2.get(i));
        }
        return RESULT;
    }

    /**
     * signum function
     *
     * @param i
     *            the function argument
     * @return -1, 0 or 1 if the argument is negative, 0 or positive
     */
    // Aside from being the most useless function ever, like ever, like !!!EVERRR!!!
    // why the fuck not using the number directly for the love of GOD
    public static int signum(int i) {
        // Problem 7 - name of the function doesn't respect the camelCase pattern
        // Problem 8 - there are no braces to indicate blocks for if else
        // Problem 9 - useless else statement
        if(i < 0)
            return -1;
        else if (i > 0)
            return 1;
        else
            return 0;
    }
}
