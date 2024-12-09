package typeAnnotatorTestData;

import java.util.Arrays;

public class QuantifiedExpressions {
    private int number;

    /*@ (* trying to override variables *)
      @ ensures (\forall int <error descr="You are not allowed to override local variables and parameters">arr</error>; 0<error descr="This operator cannot be applied to type int and type int[]"> <= </error>arr && arr < arr.length; arr[<error descr="This must be of type int or something that can be converted to int, but is int[]">arr</error>] > 0);
      @ ensures (\forall int number; 0 <= number && number < arr.length; arr[number] > 0);
      @ ensures (\forall int i; 0 <= i && i < arr.length; arr[i] > 0);
    */
    /*@ (* wrong type in body *)
      @ ensures (\forall int i; 0 <= i && i < arr.length; <error descr="This must be of type boolean, but is int">i</error>);
      @ ensures (\exists int i; 0 <= i && i < arr.length; <error descr="This must be of type boolean, but is int">i</error>);
      @ ensures (\num_of int i; 0 <= i && i < arr.length; <error descr="This must be of type boolean, but is int">i</error>) > 0;
      @ ensures (\min int i; 0 <= i && i < arr.length; <error descr="This must be of type numeric, but is boolean">arr[i] > 0</error>) > 0;
      @ ensures (\max int i; 0 <= i && i < arr.length; <error descr="This must be of type numeric, but is boolean">arr[i] > 0</error>) > 0;
      @ ensures (\product int i; 0 <= i && i < arr.length; <error descr="This must be of type numeric, but is boolean">arr[i] > 0</error>) > 0;
      @ ensures (\sum int i; 0 <= i && i < arr.length; <error descr="This must be of type numeric, but is boolean">arr[i] > 0</error>) > 0;
    */
    /*@ (* wrong type in range *)
      @ ensures (\forall int i; <error descr="This must be of type boolean, but is int">i</error>; arr[i] > 0);
      @ ensures (\exists int i; <error descr="This must be of type boolean, but is Object">new Object()</error>; arr[i] > 0);
    */
    /*@ (* empty range / no range *)
      @ ensures (\forall int i; ; arr[i] > 0);
      @ ensures (\sum int i; i) > 0; 
    */
    /*@ (* check return types of expression *)
      @ ensures (\forall int i; 0 <= i && i < arr.length; arr[i] > 0);
      @ ensures (\exists int i; 0 <= i && i < arr.length; arr[i] > 0);
      @ ensures <error descr="This must be of type boolean, but is long">(\num_of int i; 0 <= i && i < arr.length; arr[i] > 0)</error>;
      @ ensures <error descr="This must be of type boolean, but is int">(\min int i; 0 <= i && i < arr.length; i)</error>;
      @ ensures <error descr="This must be of type boolean, but is int">(\max int i; 0 <= i && i < arr.length; i)</error>;
      @ ensures <error descr="This must be of type boolean, but is int">(\product int i; 0 <= i && i < arr.length; i)</error>;
      @ ensures <error descr="This must be of type boolean, but is int">(\sum int i; 0 <= i && i < arr.length; i)</error>;
      @ ensures <error descr="This must be of type boolean, but is long">(\sum long i; 0 <= i && i < arr.length; i)</error>;
      @ ensures <error descr="This must be of type boolean, but is short">(\sum short i; 0 <= i && i < arr.length; i)</error>;
      @ ensures <error descr="This must be of type boolean, but is char">(\sum char i; 0 <= i && i < arr.length; i)</error>;
      @ ensures <error descr="This must be of type boolean, but is byte">(\sum byte i; 0 <= i && i < arr.length; i)</error>;
      @ ensures <error descr="This must be of type boolean, but is float">(\sum float i; 0 <= i && i < arr.length; i)</error>;
      @ ensures <error descr="This must be of type boolean, but is double">(\sum double i; 0 <= i && i < arr.length; i)</error>;
    */
    public int sumAll(int[] arr) {
        return 0;
    }
}
