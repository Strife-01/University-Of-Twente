package ss.week6.pizza;

import java.util.concurrent.locks.Lock;

/**
 * Implements a Chef that adds pepperoni to a pizza.
 */
public class PizzaChef implements Runnable {
    private Pizza pizza;
    /**
     * Creates a new PizzaChef that will prepare the given pizza.
     * @param pizza the pizza to prepare
     */
    public PizzaChef(Pizza pizza) {
        this.pizza = pizza;
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        // add pepperoni 5000 x
        for (int i = 0; i < 5000; i++) {
            //pizza.addPepperoni();
            pizza.addPepperoniLock();
        }
    }
}
