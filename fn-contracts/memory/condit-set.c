// checked in solutions :)
/*@ requires valid_ptrs: \valid(a) && \valid_read(b); 
    requires diff_ptrs: \separated(a, b); 

    assigns val_to_first: *a; 

    ensures second_true: \old(*b) ==> *a == 0; 
    ensures second_false: !\old(*b) ==> *a == \old(*a); 
    ensures unchanged_second: \old(*b) == *b; 
*/
void reset_1st_if_2nd_is_true(int* a, int const* b){
    if(*b) *a = 0 ;
}


int main(){
int a = 5 ;
int x = 0 ;

reset_1st_if_2nd_is_true(&a, &x);
//@ assert a == 5 ;
//@ assert x == 0 ;

int const b = 1 ;

reset_1st_if_2nd_is_true(&a, &b);
//@ assert a == 0 ;
//@ assert b == 1 ;
}