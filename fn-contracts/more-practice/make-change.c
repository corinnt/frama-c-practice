#include <limits.h>
#include <stddef.h>

enum note { N500, N200, N100, N50, N20, N10, N5, N2, N1 };
int const values[] = { 500, 200, 100, 50, 20, 10, 5, 2, 1 };

/*@ 
    predicate valid_range_rw(int* arr, size_t length) =
        0 <= length <= INT_MAX && \valid(arr + (0 .. length-1));
*/

/*@
  requires valid_range: valid_range_rw(array, length) ; 
  assigns array[0 .. length-1];
  ensures \forall size_t i; 0 <= i < length ==> array[i] == 0;
*/
void reset(int* array, size_t length){
  /*@
    loop invariant 0 <= i <= length;
    loop invariant \forall size_t j; 0 <= j < i ==> array[j] == 0;
    loop invariant \forall size_t j; i <= j < length
        ==> array[j] == \at(array[j], Pre) ; 
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
  */
  for(size_t i = 0; i < length; ++i)
    array[i] = 0;
}

// 4th requires statement was wp-suggested for rest and values
/*@ requires valid_ptr: \valid(rest) ;
    requires no_rte_rest: 0 <= *rest < INT_MAX; 
    requires normal_len: 0 <= n < 9; 
    requires separated: \separated(rest, (int const *)values + (..));

    assigns *rest ; 

    ensures *rest == \old(*rest) % values[n] ;
    ensures \old(*rest) == (\result * values[n]) + *rest ; 

    behavior remainder: 
        assumes *rest % values[n] >= 0 && *rest >= values[n] ;
        ensures (\old(*rest) - *rest) == \result * values[n] ; 
        ensures *rest == \old(*rest) % values[n]; 

    behavior note_gt_rest:
        assumes values[n] > *rest ; 
        ensures *rest == \old(*rest) ;
        ensures \result == 0;   

    disjoint behaviors; 
    complete behaviors; 
*/
int remove_max_notes(enum note n, int* rest) {
  int old_rest = *rest; 
  *rest = *rest % values[n]; 
  return (old_rest - *rest) / values[n] ; 
}  

/*@ requires valid_ptr: \valid(change + (0 .. 8));
    requires 0 < amount < INT_MAX; 
    requires 0 < received < INT_MAX;

    assigns change[0 .. 8];     

    behavior overpaid: 
        assumes amount <= received ; 
        ensures \result == 0 ; 

    behavior underpaid: 
        assumes amount > received ; 
        ensures \result == -1 ;  

    disjoint behaviors; 
    complete behaviors; 
*/
int make_change(size_t amount, size_t received, int* change){
    size_t length = 9;
    reset(change, length); 
    if (amount > received) { return -1; }; 
    int rest = received - amount; 

    /*@
        loop invariant 0 <= i <= 9 ;
        loop invariant 0 <= rest <= \at(rest, LoopEntry) <= INT_MAX ; 
        loop assigns i, rest, change[0 .. length-1] ;
        loop variant length - i ;
    */
    for (size_t i = 0; i < length; i++){ 
        //@ assert i < 9; 
        change[i] = remove_max_notes(i, &rest);
    }
    
    // assert rest == 0; 
    return 0;
}

/*

loop invariant rest == \at(rest, LoopCurrent) - (values[i] * change[i]) - \at(rest, LoopCurrent) % values[i]; 

ensures \forall size_t i; 0 <= i < length ==> change[i] == 0; 
loop invariant each_iter: \at(rest, LoopCurrent) > values[i] 
                        ==> change[i] == (\at(rest, LoopCurrent) / values[i]);
loop invariant tbd: \forall size_t j; i <= j < length 
                        ==> change[j] == 0;
*/