package semanticsAnnotatorTestData;

public class MultipleDuplicateVisibilityModifiers {
    int x = 5; //@ <error descr="You cannot have multiple specification visibility modifiers (spec_public or spec_protected)">spec_protected</error> <error descr="You cannot have multiple specification visibility modifiers (spec_public or spec_protected)">spec_public</error> <error descr="You cannot have multiple specification visibility modifiers (spec_public or spec_protected)">spec_public</error> <error descr="You cannot have multiple specification visibility modifiers (spec_public or spec_protected)">spec_protected</error>

    //@ private <error descr="You cannot have multiple visibility modifiers (public, protected or private)">public</error> <error descr="You cannot have multiple visibility modifiers (public, protected or private)">private</error> <error descr="You cannot have multiple visibility modifiers (public, protected or private)">protected</error> <error descr="You cannot have multiple visibility modifiers (public, protected or private)">public</error> invariant 10 >= 5;
}
