(* tests the multiplication via circuit *)

#use "circmult.ml";;

let rec i2n = function 0 -> O | n -> (S (i2n (n-1)));;

let rec n2i = function O -> 0 | (S n) -> 1+(n2i n);;

let _ = 
   let a = 123
   and b = 79
   in 
   let c = (n2i (mult' (i2n a) (i2n b))) in 
   print_string "Multiplication via the circuit gives :\n";
   print_int a; 
   print_string " * ";
   print_int b; 
   print_string " = "; 
   print_int c;
   print_newline();
   if c<>a*b then exit 1;;

		 

