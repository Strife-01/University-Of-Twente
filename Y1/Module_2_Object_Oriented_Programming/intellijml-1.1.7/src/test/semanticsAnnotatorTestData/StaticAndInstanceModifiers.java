package semanticsAnnotatorTestData;

public class StaticAndInstanceModifiers {

    //@ instance <error descr="You cannot use both instance and static, choose one">static</error> invariant 1 > 0;
    //@ static <error descr="You cannot use both instance and static, choose one">instance</error> invariant 1 > 0;
    //@ static invariant 1 > 0;
    //@ instance invariant 1 > 0;
}
