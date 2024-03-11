#include <limits.h>
/*@ 
    requires INT_MIN < val;

    ensures positive_value: function_result: \result >= 0;
    ensures (\old(val) >= 0 ==> \result == \old(val)) &&
    (\old(val) < 0 ==> \result == -\old(val));
    
    assigns \nothing; 

*/
int abs(int val){
    if (val < 0) {
        /*@ assert rte: signed_overflow: -2147483647 <= val; */
        return -val;
    } 
    return val;
}

/*@
    requires d_input_not_min: -217483647 - 1 < a; 
    assigns \nothing; 
*/
void foo(int a){
 int b = abs(42);
 int c = abs(-42);
 int d = abs(a); // False : "a" can be INT_MIN
 int e = abs(INT_MIN + 1); // False : the parameter must be strictly greater than INT_MIN
 }