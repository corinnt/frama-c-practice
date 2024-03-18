/* All verified! :D */

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

/*@ requires \valid(a) && \valid(b) && \valid(c) ;
    requires \separated(a, b, c); 
    assigns *a, *b, *c ;

    ensures { \old(*a), \old(*b), \old(*c) } == { *a, *b, *c }; 

    behavior all_equal: 
        assumes *a == *b == *c ; 
        ensures *a == *b == *c; 

    behavior all_uequal: 
        assumes *a != *b && *a != *c && *b != *c ; 
        ensures *a != *b && *a != *c && *b != *c ;
  
    behavior two_eq_lt: 
        assumes *a == *b < *c || 
                *a == *c < *b ||
                *b == *c < *a; 
        ensures *a == *b;  

    behavior two_eq_gt: 
        assumes *a == *b > *c || 
                *a == *c > *b ||
                *b == *c > *a; 
        ensures *b == *c; 
    
    complete behaviors ;
    disjoint behaviors ;
*/
void order_3_inc_max(int* a, int* b, int* c) {
  //in increasing order using max_ptr
  max_ptr(c, b) ;
  max_ptr(c, a) ;
  max_ptr(b, a) ;
}

/*@ requires \valid(a) && \valid(b) && \valid(c) ;
    requires \separated(a, b, c); 
    assigns *a, *b, *c ;

    ensures { \old(*a), \old(*b), \old(*c) } == { *a, *b, *c }; 

    behavior all_equal: 
        assumes *a == *b == *c ; 
        ensures *a == *b == *c; 

    behavior all_uequal: 
        assumes *a != *b && *a != *c && *b != *c ; 
        ensures *a != *b && *a != *c && *b != *c ;
  
    behavior two_eq_lt: 
        assumes *a == *b < *c || 
                *a == *c < *b ||
                *b == *c < *a; 
        ensures *a == *b;  

    behavior two_eq_gt: 
        assumes *a == *b > *c || 
                *a == *c > *b ||
                *b == *c > *a; 
        ensures *b == *c; 
    
    complete behaviors ;
    disjoint behaviors ;
*/
void order_3_inc_min(int* a, int* b, int* c) {
  min_ptr(a, b) ;
  min_ptr(a, c); 
  min_ptr(b, c);
}


/*@ requires \valid(a) && \valid(b) && \valid(c) ;
    requires \separated(a, b, c); 
    assigns *a, *b, *c ;

    ensures { \old(*a), \old(*b), \old(*c) } == { *a, *b, *c }; 

    behavior all_equal: 
        assumes *a == *b == *c ; 
        ensures *a == *b == *c; 

    behavior all_uequal: 
        assumes *a != *b && *a != *c && *b != *c ; 
        ensures *a != *b && *a != *c && *b != *c ;
  
    behavior two_eq_lt: 
        assumes *a == *b < *c || 
                *a == *c < *b ||
                *b == *c < *a; 
        ensures *b == *c;

    behavior two_eq_gt: 
        assumes *a == *b > *c || 
                *a == *c > *b ||
                *b == *c > *a; 
        ensures *a == *b;  

    complete behaviors ;
    disjoint behaviors ;
*/
void order_3_dec_max(int* a, int* b, int* c) {
  max_ptr(a, b) ;
  max_ptr(a, c); 
  max_ptr(b, c);
}

/*@ requires \valid(a) && \valid(b) && \valid(c) ;
    requires \separated(a, b, c); 
    assigns *a, *b, *c ;

    ensures { \old(*a), \old(*b), \old(*c) } == { *a, *b, *c }; 

    behavior all_equal: 
        assumes *a == *b == *c ; 
        ensures *a == *b == *c; 

    behavior all_uequal: 
        assumes *a != *b && *a != *c && *b != *c ; 
        ensures *a != *b && *a != *c && *b != *c ;
  
    behavior two_eq_lt: 
        assumes *a == *b < *c || 
                *a == *c < *b ||
                *b == *c < *a; 
        ensures *b == *c;

    behavior two_eq_gt: 
        assumes *a == *b > *c || 
                *a == *c > *b ||
                *b == *c > *a; 
        ensures *a == *b;  

    complete behaviors ;
    disjoint behaviors ;
*/
void order_3_dec_min(int* a, int* b, int* c) {
  //in decreasing order using min_ptr
  min_ptr(c, b) ;
  min_ptr(c, a) ;
  min_ptr(b, a) ;
}