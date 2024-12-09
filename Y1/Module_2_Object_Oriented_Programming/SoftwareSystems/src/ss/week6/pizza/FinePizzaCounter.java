package ss.week6.pizza;

import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/*
    In case of multithreading the conditions change a little bit because everything happens asynchronously so the checks
    might take place before or after or even at the same time the counter is updated in any way.
    It becomes less deterministic.
 */

/**
 * Simulates a pizza counter with limited space.
 */
public class FinePizzaCounter {
    private final List<Pizza> pizzas = new LinkedList<>();
    private static final int MAX_PIZZAS = 1;
    private final Lock lock = new ReentrantLock();
    private final Condition pizzaCounterCondition = lock.newCondition();

    /*@ invariant pizzas.size() >= 0 && pizzas.size() <= MAX_PIZZAS; @*/

    /**
     * Add a pizza to the counter.
     * @param pizza the pizza to add
     */
    /*@ ensures
    (pizzas.size() == \old(pizzas.size()) + 1) ==>
    (\exists int i; pizzas.get(i) == pizza && i == pizzas.size() - 1) ||
    (pizzas.size() == \old(pizzas.size()));
    */

    public void addPizza(Pizza pizza) {
        // we can only have MAX_PIZZAS pizzas on the counter
        try {
            // Create a lock to prevent race conditions
            lock.lock();
            // As long as the required condition is not respected we force the thread to wait.
            // Wait while the counter is full.
            while (pizzas.size() >= MAX_PIZZAS) {
                pizzaCounterCondition.await();
            }
            // If the counter is empty - i.e. we can still add pizza we add it and signal the thread that it is ok to proceed.
            pizzas.add(pizza);
            pizzaCounterCondition.signal();
        } catch (InterruptedException e) {
            // In case of a blocking thread we eliminate it so we don't create deadlocks.
            Thread.currentThread().interrupt();
        } finally {
            // We unlock the thread no matter what so we don't get deadlocks.
            lock.unlock();
        }
    }

    /*
        The new problem is that we get deadlocks.
        After the first delivery it stops.
     */

    /**
     * Take the first pizza from the counter.
     * @return the first pizza
     */
    /*@ ensures
    (\exists Pizza p; p == \result &&
        pizzas.size() == \old(pizzas.size()) - 1 &&
        !pizzas.contains(p))
    &&
    (\forall Pizza p1; pizzas.contains(p1) ==> \old(pizzas).contains(p1));
    */
    public Pizza takePizza() {
        try {
            // Lock the thread to prevent race conditions.
            lock.lock();
            // As long as the condition is not respected we force the thread to wait.
            while (pizzas.isEmpty()) {
                pizzaCounterCondition.await();
            }
            // When we get a new pizza we signal the thread that it can take it.
            pizzaCounterCondition.signal();
            return pizzas.remove(0);
        } catch (InterruptedException e) {
            // In case of thread hogging we kill it so we don't get deadlocks.
            Thread.currentThread().interrupt();
            return null;
        } finally {
            // Finally we unlock the method.
            lock.unlock();
        }
    }
}
