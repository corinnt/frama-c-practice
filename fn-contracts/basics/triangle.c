/*@
    requires inputs: range: 0 < first < 180 &&
                            0 < second < 180;
    
    requires positive_remainder: first + second < 180; 
    ensures sum_180: first + second + \result == 180; 
    assigns \nothing; 
*/
int last_angle(int first, int second){
    return 180 - first - second ;
}