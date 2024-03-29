// can put lists of \separated ptrs
// can do inequality chains
// NOTE: see has_all_values for set notation 

// interesting thing I noticed: joining last 3 `ensures` clauses will time out assertions
// best to separate out logical pieces (or could raise timeout limit, but that doesn't really solve the problem)

/*@ requires \valid(a) && \valid(b) && \valid(c); 
    requires \separated(a, b, c); 

    assigns *a, *b, *c; 

    ensures sorted: *a <= *b <= *c ;
    ensures has_all_values: { *a, *b, *c } == \old({ *a, *b, *c }) ;

    ensures \old(*a == *b == *c) ==> *a == *b == *c ; 
    ensures \old(*a == *b < *c || *a == *c < *b || *b == *c < *a) ==> *a == *b ; 
    ensures \old(*a == *b > *c || *a == *c > *b || *b == *c > *a) ==> *b == *c ;
*/
void order_3(int* a, int* b, int* c){
    if(*a > *b){
        int tmp = *b ; *b = *a ; *a = tmp ;
    }
    if(*a > *c){
        int tmp = *c ; *c = *a ; *a = tmp ;
    }
    if(*b > *c){
        int tmp = *b ; *b = *c ; *c = tmp ;
  }
}

/*@ assigns \nothing ; 
*/
void test(){
    int a1 = 5, b1 = 3, c1 = 4 ;
    order_3(&a1, &b1, &c1); 
    //@ assert a1 == 3 && b1 == 4 && c1 == 5 ;

    int a2 = 2, b2 = 2, c2 = 2 ;
    order_3(&a2, &b2, &c2) ;
    //@ assert a2 == 2 && b2 == 2 && c2 == 2 ;

    int a3 = 4, b3 = 3, c3 = 4 ; 
    order_3(&a3, &b3, &c3) ;
    //@ assert a3 == 3 && b3 == 4 && c3 == 4 ;

    int a4 = 4, b4 = 5, c4 = 4 ;
    order_3(&a4, &b4, &c4) ;
    //@ assert a4 == 4 && b4 == 4 && c4 == 5 ;
}