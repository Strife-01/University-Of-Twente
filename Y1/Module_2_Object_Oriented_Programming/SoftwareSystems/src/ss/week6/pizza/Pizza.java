package ss.week6.pizza;

import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Pizza with pepperoni topping.
 */
public class Pizza {
    private int pepperoni = 0;
    private final Lock lock = new ReentrantLock();

    //@ private invariant pepperoni >= 0;

    /**
     * Add pepperoni to the pizza.
     */
    //@ ensures pepperoni == \old(pepperoni) + 1;
    public void addPepperoni() {
        synchronized (this) {

        /*
            1.
            A ReentrantLock is a lock that allows the thread to call lock and unlock a resource without deadlocking.
            It will make sure that threads will not wait forever for a recursive call or something similar.
            Also, besides preventing deadlocks, it allows to cont how many times a lock has been used.
            Reentrant = can reuse
            nr of calls for lock == nr of calls for unlock ==> full unlock

            2.
            It behaves differently from synchronize as it doesn't automatically lock or unlocks the thread for the user.

            3.
            The advantage - full control.

            4.
            The disadvantage - full control. - you have to not forget to unlock all the locks to prevent deadlocks.
         */
            pepperoni += 1;
        }
    }

    /**
     * Uses a ReentrantLock to prevent race conditions.
     */
    public void addPepperoniLock() {
        //synchronized (this) {

        /*
            1.
            A ReentrantLock is a lock that allows the thread to call lock and unlock a resource without deadlocking.
            It will make sure that threads will not wait forever for a recursive call or something similar.
            Also, besides preventing deadlocks, it allows to cont how many times a lock has been used.
            Reentrant = can reuse
            nr of calls for lock == nr of calls for unlock ==> full unlock

            2.
            It behaves differently from synchronize as it doesn't automatically lock or unlocks the thread for the user.

            3.
            The advantage - full control.

            4.
            The disadvantage - full control. - you have to not forget to unlock all the locks to prevent deadlocks.
         */
        lock.lock();
        pepperoni += 1;
        lock.unlock();
        //}
    }

    /**
     * Returns a textual representation of this pizza.
     * @return the textual representation
     */
    //@ pure;
    @Override
    public String toString() {
        return "pizza with " + pepperoni + " pepperoni";
    }
}
