#include <limits.h>

/*@ 
    requires INT_MIN < x + y < INT_MAX; 
    ensures correct_sum: function_result: \result == x + y; 
    assigns \nothing; 

*/
int add(int x, int y){
 return x+y ;
}