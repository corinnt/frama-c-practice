/*@ requires \valid(a) && \valid(b); 
    
    assigns *a, *b; 
    
    ensures is_max: *a >= *a && *a >= *b; 
    ensures one_of_the_two: *a == \old(*a) || \result == *b; 
*/
void max_ptr(int* a, int* b){
    //TODO: fix
    int temp = a; 
    *a = (*a < *b) ? *b : *a ;
    *b = (*temp > *b) ? *b : *temp ;
}

extern int h ;

int main(){
  h = 42 ;

  int a = 24 ;
  int b = 42 ;

  int x = max_ptr(&a, &b) ;

  //@ assert x == 42 ;
  //@ assert h == 42 ;
}
