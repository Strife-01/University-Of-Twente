package ss.week4.calculator.reference;

import java.io.*;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;
import ss.TikTakToe.Player;
import ss.week4.calculator.DivideByZeroException;
import ss.week4.calculator.StackEmptyException;

public class MyStreamCalculator implements ss.calculator.Calculator, ss.week4.calculator.StreamCalculator {
    List<Double> list = new LinkedList<>();
    /**
     * Push the given value on the stack.
     *
     * @param value the value to push on the stack
     */

    @Override
    public void push(double value) {
        list.add(value);
    }

    /**
     * Pop a value from the stack.
     *
     * @return the value that was on the top of the stack
     * @throws StackEmptyException if the stack is empty
     */
    @Override
    public double pop() throws StackEmptyException {
        if (list.isEmpty()) {
            throw new StackEmptyException("The stack is empty");
        }
        return list.removeLast();
    }

    /**
     * Checks first value from the stack, but it doesn't mutate the stack.
     *
     * @return the value that is on the top of the stack
     * @throws StackEmptyException if the stack is empty
     */
    @Override
    public double peek() throws StackEmptyException {
        if (list.isEmpty()) {
            throw new StackEmptyException("The stack is empty...");
        }
        return list.getLast();
    }

    /**
     * Remove two values from the top of the stack, add them, then push the result on top of the stack.
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    @Override
    public void add() throws StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to add");
        }
        push(pop() + pop());
    }

    /**
     * Remove value a from top of the stack, then value b from top of the stack,
     * then compute b-a and push the result on top of the stack
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    @Override
    public void sub() throws StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to add");
        }
        double x = pop();
        double y = pop();
        push(y - x);
    }

    /**
     * Remove two values from the top of the stack, multiply them, then push the result on top of the stack
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least two values
     */
    @Override
    public void mult() throws StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to add");
        }
        push(pop() * pop());
    }

    /**
     * Remove value a from top of the stack, then value b from top of the stack,
     * then compute b/a  and push the result on top of the stack
     * If a was zero, then push the value "Double.NaN" on top of the stack and throw the exception.
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException   if the stack does not have at least two values
     * @throws DivideByZeroException if value a had value 0
     */
    @Override
    public void div() throws DivideByZeroException, StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to add");
        }
        double x = pop();
        double y = pop();
        if (x == 0) {
            push(Double.NaN);
            throw new DivideByZeroException("/0 :(((");
        }
        push(y / x);
    }

    /**
     * Remove value a from top of the stack, then value b from top of the stack,
     * then compute b%a  and push the result on top of the stack
     * If a was zero, then push the value "Double.NaN" on top of the stack and throw the exception.
     * If there are less than two values on the stack, the stack remains unchanged and
     * a StackEmptyException is thrown.
     *
     * @throws StackEmptyException   if the stack does not have at least two values
     * @throws DivideByZeroException if value a had value 0
     */
    @Override
    public void mod() throws DivideByZeroException, StackEmptyException {
        if (list.size() < 2) {
            throw new StackEmptyException("You need at least 2 values to perform modulo");
        }
        double x = pop();
        double y = pop();
        if (x == 0) {
            push(Double.NaN);
            throw new DivideByZeroException("Modulo by zero is undefined");
        }
        push(y % x);
    }

    /**
     * Checks value a from top of the stack,
     * then pushes a duplicate on top of the stack
     * If less than 1 value then a StackEmptyException is thrown.
     *
     * @throws StackEmptyException if the stack does not have at least one value
     */
    @Override
    public void dup() throws StackEmptyException {
        if (list.isEmpty()) {
            throw new StackEmptyException("The list is empty..");
        }
        push(peek());
    }

    /**
     * A stream wrapper around the calculator that reads commands from the given Reader and writes output to the Writer
     * Each command is a single line, for example:
     * - "push 100.5"
     * - "pop"
     * - "add"
     * - "sub"
     * - "mult"
     * - "div"
     * After a pop, the obtained value is written on a single line to the output.
     * If there is an error, a line is written starting with "error: " followed by an error message
     */
    /**
     * Process all commands read from the given input, and write the result(s) to the given output
     *
     * @param input  the Reader to read commands from
     * @param output the Writer to write output to
     */
    @Override
    public void process(Reader input, Writer output) {
        String data = "";
        int dataSize = 0;
        try {
            int c;
            while ((c = input.read()) != -1) {
                String s = Character.toString(c);
                if (s.equals("\n")) {
                    if (dataSize > 0 && data.charAt(dataSize - 1) == '\n') {
                        data = data.concat("invalid\n");
                    } else {
                        data = data.concat(s);
                    }
                } else {
                    data = data.concat(s);
                }
                dataSize++;
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

        System.out.println(data);

        String[] dataArray = data.split("\\s+");
        for (int i = 0; i < dataArray.length; i++) {
            switch (dataArray[i].toLowerCase()) {
                case "push":
                    try {
                        push(Double.parseDouble(dataArray[++i]));
                    } catch (NumberFormatException e) {
                        writeError(output);
                    }
                    break;
                case "pop":
                    try {
                        String result = pop() + "\n";
                        output.append(result);
                    } catch (StackEmptyException e) {
                        writeError(output);
                    } catch (IOException e) {
                        System.out.println("ononono");
                    }
                    break;
                case "add":
                    try {
                        add();
                    } catch (StackEmptyException e) {
                        writeError(output);
                    }
                    break;
                case "sub":
                    try {
                        sub();
                    } catch (StackEmptyException e) {
                        writeError(output);
                    }
                    break;
                case "mult":
                    try {
                        mult();
                    } catch (StackEmptyException e) {
                        writeError(output);
                    }
                    break;
                case "div":
                    try {
                        div();
                    } catch (DivideByZeroException | StackEmptyException e) {
                        writeError(output);
                    }
                    break;
                case "mod":
                    try {
                        mod();
                    } catch (DivideByZeroException | StackEmptyException e) {
                        writeError(output);
                    }
                    break;
                case "dup":
                    try {
                        dup();
                    } catch (StackEmptyException e) {
                        writeError(output);
                    }
                    break;
                default:
                    writeError(output);
                    break;
            }
            try {
                System.out.println(peek());
            } catch (StackEmptyException e) {
                System.out.println("err");
            }
        }
    }

    private void writeError(Writer output) {
        try {
            output.append("error: ... \n");
        } catch (IOException ex) {
            System.out.println("ononono");
        }
        try {
            output.flush();
        } catch (IOException ex) {
            System.out.println("ononono");
        }
    }

    public static void main(String[] args) throws IOException, StackEmptyException {
        MyStreamCalculator calculator = new MyStreamCalculator();
        calculator.process(new FileReader("src/ss/week4/calculator/reference/calculatorinstructions"), new StringWriter());
        BufferedReader reader;
        Scanner sc = new Scanner(System.in);
        Writer writer = new PrintWriter(System.out);
        String str = "";
        calculator.list = new LinkedList<>();
        while (true) {
            System.out.print("> ");
            str = sc.nextLine();
            if (str.equalsIgnoreCase("exit")) {
                break;
            }
            reader = new BufferedReader(new StringReader(str));
            calculator.process(reader, writer);
        }

    }
}
