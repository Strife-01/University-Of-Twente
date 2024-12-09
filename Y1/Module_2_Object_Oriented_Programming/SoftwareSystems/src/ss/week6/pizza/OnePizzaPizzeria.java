package ss.week6.pizza;

public class OnePizzaPizzeria {
    public static void main(String[] args) {
        // Create a new pizza
        Pizza pizza = new Pizza();
        // Create 3 chefs all working on the same pizza.
        PizzaChef chef1 = new PizzaChef(pizza);
        PizzaChef chef2 = new PizzaChef(pizza);
        PizzaChef chef3 = new PizzaChef(pizza);
        // Create a new thread for each chef individually
        Thread chefTread1 = new Thread(chef1);
        Thread chefTread2 = new Thread(chef2);
        Thread chefTread3 = new Thread(chef3);
        // Start the threads
        chefTread1.start();
        chefTread2.start();
        chefTread3.start();
        // Run thread.join()
        try {
            chefTread1.join();
            chefTread2.join();
            chefTread3.join();
            // InterruptedException is thrown when a thread is performing a blocking operation. Such as sleeping or waiting.
            // It signals that the thread should stop what it is doing and possibly terminate.
            // Occurs during operations like sleep(), wait(), or join()
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
        // Print pizza
        System.out.println(pizza.toString());
        // The reason why it prints different results it's because the threads are asynchronous and when we
        // read different values. They are independently managed by the cpu scheduler based on different algorithms.
        // Depending on the moment when we read the value mutated by the threads we can read different values if the
        // threads are still working on them.
        // Concurrent Thread execution.
        // Race conditions on shared object pizza.
        // Non-deterministic scheduling of threads.
        // Accessing the pizza by the two threads at the same time
        // If we synchronize the pizza then we will only get the max value.

        // Multiple threads can access multiple pizza at the same time because the lock is on the pizza object on
        // this keyword.
    }
}
