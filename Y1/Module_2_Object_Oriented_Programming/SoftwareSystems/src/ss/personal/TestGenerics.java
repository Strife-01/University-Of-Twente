package ss.personal;

public class TestGenerics<T, M> {
    private T generic;
    private M generic2;

    private T getGeneric() {
        return generic;
    }

    private M getGeneric2() {
        return generic2;
    }

    private void setGeneric(T generic) {
        this.generic = generic;
    }

    private void setGeneric2(M generic2) {
        this.generic2 = generic2;
    }
}
