/* assigns \nothing
*/
void minus_loop() {
    int x = -20 ;
    /*@
        loop variant -x ; 
    */
    while (x < 0){
        x += 4 ;
    }
}

/* assigns \nothing
*/
void minus_loop_2() {
    int x = -20 ;
    int rm = 5; 
    /*@
        loop invariant (-rm) * 4 == x; 
        loop variant rm ; 
    */
    while (x < 0){
        x += 4 ;
        rm -- ; 
    }
}