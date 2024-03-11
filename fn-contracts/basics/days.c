/*@ 
    requires input_range: 1 <= month <= 12; 

    ensures result_options: \result \in {28, 30, 31}; 
    ensures correct_day: month \in {1, 3, 5, 7, 8, 10, 12} ==> \result == 31 &&
                         month == 2  ==> \result == 28 &&
                         month \in { 4, 6, 9, 11 } ==> \result == 30; 
    assigns \nothing; 

*/
int day_of(int month){
    int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
    return days[month-1] ;
}

