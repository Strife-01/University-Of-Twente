package typeAnnotatorTestData;

public class SignalsExceptionReferences {
    /*@
        signals(ArithmeticException e) true;
        signals(NullPointerException e) true;
        signals (Exception e) true;
        signals(<error descr="This is not an exception class">TestNoException</error> e) true;
        signals(TestException e) true;
        signals(TestException2 e) true;
        signals(<error descr="This exception (or a superclass or subclass of it) should be mentioned in the throws clause of this method">TestException3</error> e) true;
        signals(<error descr="This class could not be resolved, did you forget to import it?">NonExistent</error> e) true ;
        signals(<error descr="This class could not be resolved, did you forget to import it?">test</error> e) true ;
     */
    public int div(int a, int b) throws TestException {
        return a / b;
    }

    /*@
        signals_only ArithmeticException,
            NullPointerException,
            Exception,
            <error descr="This is not an exception class">TestNoException</error>,
            TestException,
            TestException2,
            <error descr="This exception (or a superclass or subclass of it) should be mentioned in the throws clause of this method">TestException3</error>,
            <error descr="This class could not be resolved, did you forget to import it?">NonExistent</error>,
            <error descr="This class could not be resolved, did you forget to import it?">test</error>;
     */
    public int div2(int a, int b) throws TestException {
        return a / b;
    }

    private static class TestNoException {

    }

    private static class TestException extends Exception {

    }

    private static class TestException2 extends ArithmeticException {

    }

    private static class TestException3 extends Exception {

    }
}


