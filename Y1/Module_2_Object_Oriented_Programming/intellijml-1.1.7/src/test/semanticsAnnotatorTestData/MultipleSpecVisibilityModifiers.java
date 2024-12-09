package semanticsAnnotatorTestData;

public class MultipleSpecVisibilityModifiers {
    //@ <error descr="You cannot have multiple specification visibility modifiers (spec_public or spec_protected)">spec_protected</error> <error descr="You cannot have multiple specification visibility modifiers (spec_public or spec_protected)">spec_public</error>
    private int x = 5;

    //@ spec_protected
    //@ <error descr="You cannot have multiple specification visibility modifiers (spec_public or spec_protected)">spec_public</error>
    private int y = 5;

    //@ spec_protected
    private int z = 5; //@ <error descr="You cannot have multiple specification visibility modifiers (spec_public or spec_protected)">spec_public</error>


}
