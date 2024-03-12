#include <stddef.h>

/*@ requires \valid(x) && \valid(y);

    assigns *x, *y;

    ensures *x == \old(*y) && *y == \old(*x);
*/
void swap(int* x, int* y){
    int temp = *x; 
    *x = *y; 
    *y = temp; 
}

/*@ requires arr_pointer: \valid(arr + (0 .. n)); 

    assigns arr[0 .. n - 1]; 

    predicate inc_pair(integer x, integer y) = x <= y; 

    ensures \forall size_t i; 0 < i < n && arr[i]
    ensures \forall size_t i; 0 < i < n && inc_pair([i - 1], [i]); 
*/
void selection_sort(int arr[], size_t n) 
{ 
    int i, j, min_idx; 
    for (i = 0; i < n - 1; i++) { 
        // Find the min elt in original arr
        min_idx = i; 
        for (j = i + 1; j < n; j++) 
            if (arr[j] < arr[min_idx]) 
                min_idx = j; 
  
        // Swap the found min elt w/ the first elt 
        swap(&arr[min_idx], &arr[i]); 
    } 
} 

/*@ requires \valid(a) && \valid(b) && \valid(c); 
    requires \separated(a, b, c); 

    assigns *a, *b, *c; 

    ensures \old(*a == *b == *c) ==> *a == *b == *c ;
    ensures \old(*a == *b < *c || *a == *c < *b || *b == *c < *a) ==> *a == *b ;
    ensures \old(*a == *b > *c || *a == *c > *b || *b == *c > *a) ==> *b == *c ;
*/
void order_3(int* a, int* b, int* c){
    int arr[] = {*a, *b, *c}; 
    int length = sizeof(arr) / sizeof(arr[0]); 
    selection_sort(arr, length); 
    *a, *b, *c = arr[0], arr[1], arr[2]; 
}