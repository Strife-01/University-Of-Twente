package ss.week6.pizza;

import java.util.LinkedList;
import java.util.List;

/**
 * Simulates a pizza counter with limited space.
 */
public class PizzaCounter {
    private final List<Pizza> pizzas = new LinkedList<>();
    private static final int MAX_PIZZAS = 1;

    /**
     * Add a pizza to the counter.
     * @param pizza the pizza to add
     */
    public synchronized void addPizza(Pizza pizza) {
        // we can only have MAX_PIZZAS pizzas on the counter
        if (pizzas.size() < MAX_PIZZAS) {
            pizzas.add(pizza);
            notifyAll();
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
    public synchronized Pizza takePizza() {
        if (pizzas.isEmpty()) {
            try {
                wait();
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
        return pizzas.remove(0);
    }
}
