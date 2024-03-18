//example from JP where frama-c proves true, but it misbehaves if your pointers overlap
/*@                                                                                 
  requires \valid(a) && \valid(b);                                               
                                                                                 
  assigns *a, *b;                                                                
                                                                                 
  ensures *a >= *b;                                                              
  ensures *a >= \old(*a) && *a >= \old(*b);                                      
  ensures *b <= \old(*a) && *b <= \old(*b);                                      
                                                                                 
  behavior b1:                                                                   
    assumes *a < *b;                                                             
    ensures *b == \old(*a) && *a == \old(*b);                                    
                                                                                 
  behavior b2:                                                                   
    assumes *a >= *b;                                                            
    ensures *b == \old(*b) && *a == \old(*a);                                    
                                                                                 
  complete behaviors;                                                            
  disjoint behaviors;                                                            
*/                                                                               
void max_ptr(int *a, int *b) {                                                   
  if (*a < *b) {                                                                 
    int tmp = *b;                                                                
    *b = *a;                                                                     
    *a = tmp;                                                                   
  }
                                                                           
}