(* Exercise 1 *)

(* linear without pattern matching *)
fun linear1 (A:real, B:real, X : real list) =
    (* testing when list is null *)
    if (null X) then X
    (* recursion *)
    else (A + hd(X) * B)::linear1(A, B, tl(X));

(* linear with pattern matching *)
(* first testing if list is null *)
fun linear2 (A:real, B:real, [] : real list) = nil
(* Doing recursion with pattern matching *)
  | linear2 (A:real, B:real, h::hr) = (A + h * B)::linear1(A, B, hr);

(* End of Exercise 1 *)

(* Exercise 2 *)

(* a) Defining type flight *)
type flight = {number: int, airline: string, from: string, to: string, duration: real, passengers: string list};

(* b) updating duration *)
(* creating exception *)
exception NegativeNumberNotAllowed

fun updateD(D, F:flight) = 
    if D >= 0.0 then
      (* returning a flight object with new duration D *)
      { number=(#number(F)), airline=(#airline(F)), from=(#from(F)), to=(#to(F)), duration=D, passengers=(#passengers(F)) }:flight
    else
      (* raising exception for negative numbers *)
      raise NegativeNumberNotAllowed


(* c) removing Passenger *)

(* creating PassengerNotFound exception *)
exception PassengerNotFound

(* Here I create a function to use with passengers array *)
(* Then I test it (using pattern matching) and assign this result to `passengers` *)
(* If passengers has the same length as the initial array, the searched passenger wasn't found *)
(* Or return the new modified flight *)
fun removePassenger(P, F:flight) =
  (* Pattern matching with empty array *)
  let fun deletePassenger(_, []) = []
    (* iterating array *)
    | deletePassenger(P, h::hr) = 
      (* testing string with the searched person P *)
      if h = P then deletePassenger(P, hr)
      (* if the current person and the searched one arent the same *)
      else h::deletePassenger(P, hr)
    in
      let 
        (* assigning passengers list so it's possible to use its length without calling the function twice *)
        val passenger = deletePassenger(P, (#passengers(F)))
      in
        (* testing the length and returning list or raise exception *)
        if length(passenger) = length((#passengers(F))) then
          raise PassengerNotFound
        else 
          {number=(#number(F)), airline=(#airline(F)), from=(#from(F)), to=(#to(F)),duration=(#duration(F)),passengers=passenger}:flight
      end
    end;


(* d) fastest *)

(* creating exception *)
exception FlightNotFound
 
(* this aux function returns available flight, that is flights that correspond to the search criteria *)
fun getFlights(A, B, []) = []
|   getFlights(A, B, f::fs:flight list) =
        if (#from(f)) = A andalso (#to(f)) = B then f::getFlights(A, B, fs)
        else getFlights(A, B, fs);

(* returning tuple with the shortest duration time *)
fun shortest [] = raise FlightNotFound
|   shortest([f]:flight list) = (#duration(f), #number(f))
|   shortest(f::fs:flight list) =
    (* comparing reals using Real.min *)
    if Real.==(Real.min(#1(shortest(fs)), #duration(f)), #duration(f)) then
        (#duration(f), #number(f))
    else
        (#1(shortest(fs)), #2(shortest(fs)))

(* pattern matching with empty list and raising exception then *)
fun fastest(_, _, []) = raise FlightNotFound
  | fastest(A, B, F:flight list) = shortest(getFlights(A, B, F));

(* End of Exercise 2 *)

(* Exercise 3 - handling exception *)

(* Testing if flight is the same *)
fun isSameFlight (N, A, F:flight) = if N = #number(F) andalso A = #airline(F) then true else false;

(* looking for flights and returning true if it's the same *)
fun findFlights(_,_,[]) = false
  | findFlights(N:int, A:string, f::fs: flight list) =
    if isSameFlight(N, A, f) then true
    (* Recursiveness until it's true or false *)
    else findFlights(N, A, fs);

fun updateList(_, []) = []
  | updateList(P:string*int*string, f::fs: flight list) = 
    (* testing flight *)
    if isSameFlight(#2(P), #3(P), f) then 
      let 
        (* removing passenger *)
        val passenger = removePassenger(#1(P), f) 
        (* handling exception *)
        handle PassengerNotFound => (f)
      in passenger::updateList(P, fs) end
    (* recursiveness if it isnt the same flight *)
    else
      updateList(P, fs);

fun updateAux([],_) = []
  | updateAux(l::ls, F: flight list) = updateList(l, F)@updateAux(ls, F);

(* iterating list and looking for exceptions using findFlight *)
fun getExceptions([],L2) = []
  | getExceptions(L1,[]) = L1
  | getExceptions(L1::RL1:(string*int*string) list,L2: flight list) = 
    let val
      isFlight = findFlights(#2 L1,#3 L1, L2)
    in 
      if isFlight then L1::getExceptions(RL1, L2)
      else getExceptions(RL1, L2)
    end;

(* Function that calls all other functions and returns tuple with exceptions and updated flights *)
fun updatePassengers(L1, L2) = (getExceptions(L1, L2), updateAux(L1, L2));

(* end of exercise 3 *)

(* Exercise 4 - variant types *)

(* a) defining length datatype *)
datatype length = meters of real
              |   inches of real
              |   yards of real
              |   feet of real
              |   centimeters of real;

(* b) defining convert:length *)
fun convert (meters v) = (v * 39.370)
  | convert (yards v) = (v * 36.0)
  | convert (feet v) = (v * 12.0)
  | convert (centimeters v) = (v * 0.393701)
  | convert (inches v) = v;

(* c) defining totalLength *)
fun totalLength ([]) = 0.0
  | totalLength (h::hs:length list) = convert(h) + totalLength(hs);

(* end of exercise 4 *)

(* Exercise 5 *)

(* a) defining tree *)
datatype 'a RBtree = Leaf of 'a
               | BlackNode of 'a RBtree * 'a RBtree  * 'a RBtree * int
               | RedNode of 'a RBtree * 'a RBtree * int;

(* b) attached *)
(* 
The tree has type BTree:
Leaf(RedNode(BlackNode(Leaf(1), Leaf(1), Leaf(1), ~1), RedNode(Leaf(1), Leaf(1), 40), 10));
*)


(* c) defining largestRed(T) *)

fun largestRed (Leaf(_)) = 0
    (* pattern matching for RedNodes, and recursiveness until it's a leaf *)
  | largestRed (RedNode(V1, V2, V3)) = Int.max(largestRed(V1), Int.max(largestRed(V2), V3))
    (* pattern matching for BlackNodes, and recursiveness until it's a leaf *)
  | largestRed (BlackNode(V1, V2, V3, _)) = Int.max(largestRed(V1), Int.max(largestRed(V2), Int.max(largestRed(V3), 0)));

(* d) defining addTree(N, T) *)

(* creating exception *)
exception IllegalValue
fun addTree(N, Leaf(V)) = Leaf(N + V)
    (* pattern matching for BlackNodes, and recursiveness until it's a leaf *)
  | addTree(N, BlackNode(V1, V2, V3, V4)) = 
      (* raises an exception if it's not a negative value *)
      if (V4 + N) > 0 then raise IllegalValue
        (* recursiveness until it's a leaf *)
      else BlackNode(addTree(N, V1), addTree(N, V2), addTree(N, V3), V4 + N)
  | addTree(N, RedNode(V1, V2, V3)) = 
      (* raises an exception if it's not a positive value *)
      if (V3 + N) < 0 then raise IllegalValue
        (* recursiveness until it's a leaf *)
      else RedNode(addTree(N, V1), addTree(N, V2), V3 + N);

(* e) defining mapTree(F,T) *)    
(* it returns the same tree with function F applied to every single node *)
fun mapTree (F, Leaf(V)) = Leaf(F(V))
  | mapTree (F, BlackNode(V1, V2, V3, V4)) = BlackNode(mapTree(F, V1), mapTree(F, V2), mapTree(F, V3), F(V4))
  | mapTree (F, RedNode(V1, V2, V3)) = RedNode(mapTree(F, V1), mapTree(F, V2), F(V3));

(* Exercise 6 - references and iteration *)

(* defining exception to be used in exercise 6 *)
exception ElementOutOfRange

(* a) functional implementation *)
fun updateList1(_, _, []) = []
  | updateList1(X, N, h::hs:real list) = 
    (* raising exception when N is bigger than list length *)
    if N > length(h::hs) then raise ElementOutOfRange
    (* returning the summed real number *)
    else if N = 1 then (h + X)::hs
    (* iterating through the list and subtracting N so it can be 1 in the right iteration *)
    else h::updateList1(X, N-1, hs);

(* b) Functional/Procedural *)
fun updateList2 (_, _, []) = raise ElementOutOfRange
  | updateList2 (X, N, [h]) = if N = 1 then (h := !h + X) else raise ElementOutOfRange
  (* assigning sum to reference *)
  | updateList2 (X, 1, h::hs:real ref list) = (h := !h + X)
  | updateList2 (X, N, h::hs:real ref list) =
    (* raising exception when N is bigger than list length *)
    if N > length(h::hs) then raise ElementOutOfRange
    else (updateList2(X, N - 1, hs));


(* c) Procedural  *)
fun updateList3(X:real, N, L:real ref list) =
    (* getting element in list L*)
    let val h = List.nth(L, N-1)
    (* assigning sum to reference *)
    in (h := X + !h):unit end;



