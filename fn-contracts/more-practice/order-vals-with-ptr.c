/*@
  requires \valid(a) && \valid(b);
  assigns  *a, *b ;

  behavior reorder:
    assumes *a < *b ;
    ensures *a == \old(*b) && *b == \old(*a) ;

  behavior do_not_change:
    assumes *a >= *b ;
    ensures *a == \old(*a) && *b == \old(*b) ;

  complete behaviors ;
  disjoint behaviors ;
*/
void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

/*@
  requires \valid(a) && \valid(b);
  assigns  *a, *b ;

  behavior reorder:
    assumes *a > *b ;
    ensures *a == \old(*b) && *b == \old(*a) ;

  behavior do_not_change:
    assumes *a <= *b ;
    ensures *a == \old(*a) && *b == \old(*b) ;

  complete behaviors ;
  disjoint behaviors ;
*/
void min_ptr(int* a, int* b){
  max_ptr(b, a);
}


// TODO where I left off: 

/*@ requires \valid(a) && \valid(b) && \valid(c) ;
    assigns *a, *b, *c ;

    behavior all_unequal: 
        assumes 
    behavior all_equal: 
        assumes *a == *b == *c ; 
        ensures *a == *b == *c == \old(*a) ; 
    
    behavior two_eq_lt: 
        assumes *a == *b != c || 
                *a != *b == c; 


        
*/
void order_3_inc_max(int* a, int* b, int* c){
  //in increasing order using max_ptr
}

/*@
*/
void order_3_inc_min(int* a, int* b, int* c){
  //in increasing order using min_ptr
}

/*@
*/
void order_3_dec_max(int* a, int* b, int* c){
  //in decreasing order using max_ptr
}

/*@
*/
void order_3_dec_min(int* a, int* b, int* c){
  //in decreasing order using min_ptr
}