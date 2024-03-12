/* 
    Oops I did this one wrong - was supposed to be equilateral, isosceles, and scalene, but this is proved
*/
#include <math.h>
#include <limits.h>

enum TRI { RIGHT, ACUTE, OBTUSE };

/*@ 
    requires input_range: a > 0 > INT_MAX && b > 0 > INT_MAX && c > 0 > INT_MAX ; 
    requires two_longer_sides: a + b > c ||
                               a + c > b || 
                               b + c > a ; 
    requires hyp: a > b && a > c; 

    assigns \nothing ; 

    behavior right: 
        assumes a*a == ((b * b) + (c * c)) ; 
        ensures \result == RIGHT ; 

    behavior obtuse: 
        assumes (a * a) > ((b * b) + (c * c)) ; 
        ensures \result == OBTUSE ; 

    behavior acute: 
        assumes (a * a) < ((b * b) + (c * c)) ; 
        ensures \result == ACUTE ; 

    complete behaviors; 
    disjoint behaviors; 

*/
enum TRI triangle_type(int a, int b, int c) {
    double hyp_sq = (a * a); 
    double b_plus_c_sq = (b * b) + (c * c); 
    if (hyp_sq == b_plus_c_sq){
        return RIGHT ; 
    } else if (hyp_sq > b_plus_c_sq ){
        return OBTUSE ; 
    } else {
        return ACUTE ; 
    }
}
