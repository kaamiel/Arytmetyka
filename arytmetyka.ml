(*  Zadanie 1: Arytmetyka       *)
(*  autor: Kamil Dubil, 370826  *)
(*  reviewer: Filip Mikina      *)

(* Typ reprezentujący niedokładne wartości. *)
(* dla w roznego od nan jest w = [greater_than, less_than] *)
(* albo w = (neg_infinity, less_than] u [greater_than, infinity) *)
type wartosc = {greater_than: float; less_than: float}

(* czy wartosc powinna byc traktowana jako nie-liczba *)
let is_nan w =
    (compare w.greater_than nan) = 0 || (compare w.less_than nan) = 0

(* czy wartosc jest zbiorem spojnym *)
let is_connected w =
    (not (is_nan w)) && (w.greater_than <= w.less_than)

(* najmniejsza z czterech liczb;
pomija nan, minimum nan nan nan nan = infinity *)
let rec minimum a b c d =
    match (compare a nan, compare b nan, compare c nan, compare d nan) with
        | (0, _, _, _) -> minimum infinity b c d
        | (_, 0, _, _) -> minimum a infinity c d
        | (_, _, 0, _) -> minimum a b infinity d
        | (_, _, _, 0) -> minimum a b c infinity
        | (_, _, _, _) -> min (min a b) (min c d)

(* najwieksza z czterech liczb; *)
(* pomija nan, maksimum nan nan nan nan = neg_infinity *)
let rec maksimum a b c d =
    match (compare a nan, compare b nan, compare c nan, compare d nan) with
        | (0, _, _, _) -> maksimum neg_infinity b c d
        | (_, 0, _, _) -> maksimum a neg_infinity c d
        | (_, _, 0, _) -> maksimum a b neg_infinity d
        | (_, _, _, 0) -> maksimum a b c neg_infinity
        | (_, _, _, _) -> max (max a b) (max c d)

(* 1. /. 0. = infinity; 1. /. (-0.) = neg_infinity *)
let zero_to_neg_zero = function
    | 0. -> (-0.)
    | x -> x

let neg_zero_to_zero = function
    | -0. -> (0.)
    | x -> x

(*****************************************************************************)

(* wartosc_dokladnosc x p = x +/- p% *)
(* war.pocz.: p >= 0                 *)
let wartosc_dokladnosc x p =
    if p < 0. then failwith "Blad, dokladnosc musi byc nieujemna"
    else {greater_than = x -. p /. 100. *. (abs_float x);
        less_than = x +. p /. 100. *. (abs_float x)}

(* wartosc_od_do x y = [x;y]         *)
(* war.pocz.: x <= y                 *)
let wartosc_od_do x y =
    if x > y then failwith "Blad, musi byc x<=y"
    else {greater_than = x; less_than = y}

(* wartosc_dokladna x = [x;x]        *)
let wartosc_dokladna x =
    if x = neg_infinity || x = infinity
        then failwith "Blad, argument musi byc rzeczywisty"
    else {greater_than = x; less_than = x}

(*****************************************************************************)

(* in_wartosc w x = x \in w *)
let in_wartosc w x =
    if is_nan w then false
    else (is_connected w && w.greater_than <= x && x <= w.less_than) ||
        (not (is_connected w) && (w.greater_than <= x || x <= w.less_than))

(* min_wartosc w = najmniejsza możliwa wartość w,   *)
(* lub neg_infinity jeśli brak dolnego ograniczenia.*)
let min_wartosc w =
    if is_nan w then nan
    else if is_connected w then w.greater_than
    else neg_infinity

(* max_wartosc w = największa możliwa wartość w,    *)
(* lub infinity jeśli brak górnego ograniczenia.    *)
let max_wartosc w =
    if is_nan w then nan
    else if is_connected w then w.less_than
    else infinity

(* środek przedziału od min_wartosc do max_wartosc, *)
(* lub nan jeśli min i max_wartosc nie są określone.*)
let sr_wartosc w =
    (* if is_nan w then nan else *)
    (min_wartosc w +. max_wartosc w) /. 2.

(*****************************************************************************)

(* suma teoriomnogosciowa wartosci; *)
(* war.pocz.: argumenty takie, by suma dawala sie reprezentowac jako wartosc *)
let rec union a b =
    if (is_nan a) || (is_nan b) then wartosc_dokladna nan
    else match (is_connected a, is_connected b) with
    (* a i b spojne *)
        | (true, true) ->
            if (max_wartosc a < min_wartosc b) then
                (* suma rozlacznych polprostych *)
                if (min_wartosc a) = neg_infinity && (max_wartosc b) = infinity
                    then {greater_than = min_wartosc b;
                        less_than = max_wartosc a}
                else failwith "Blad1, wynik musi byc typu wartosc"
            else if (max_wartosc b < min_wartosc a) then union b a
            (* suma odcinkow/polprostych o niepustym przecieciu *)
            else wartosc_od_do
                (min (min_wartosc a) (min_wartosc b))
                (max (max_wartosc a) (max_wartosc b))
    (* a spojne, b niespojne *)
        | (true, false) ->
            if (min_wartosc a > b.less_than) &&
                (max_wartosc a < b.greater_than)
                then failwith "Blad2, wynik musi byc typu wartosc"
            else if min_wartosc a <= b.less_than then union
                (union (wartosc_od_do neg_infinity b.less_than) a)
                (wartosc_od_do b.greater_than infinity)
            else union
                (wartosc_od_do neg_infinity b.less_than)
                (union (wartosc_od_do b.greater_than infinity) a)
    (* a niespojne, b spojne *)
        | (false, true) -> union b a
    (* a i b niespojne *)
        | (false, false) ->
            if (a.greater_than <= b.less_than) || (b.greater_than <= a.less_than)
                then wartosc_od_do neg_infinity infinity
            else {greater_than = min a.greater_than b.greater_than;
                less_than = max a.less_than b.less_than}

let rec plus a b =
    if (is_nan a) || (is_nan b) then wartosc_dokladna nan
    else match (is_connected a, is_connected b) with
    (* a i b spojne *)
        | (true, true) -> wartosc_od_do
            (min_wartosc a +. min_wartosc b)
            (max_wartosc a +. max_wartosc b)
    (* a i b niespojne *)
        | (false, false) -> wartosc_od_do neg_infinity infinity
    (* a spojne, b niespojne *)
        | (true, false) -> union
            (plus a (wartosc_od_do b.greater_than infinity))
            (plus a (wartosc_od_do neg_infinity b.less_than))
    (* a niespojne, b spojne *)
        | (false, true) -> plus b a

let rec razy a b =
    if (is_nan a) || (is_nan b) then wartosc_dokladna nan
    else if a = (wartosc_dokladna 0.) || b = (wartosc_dokladna 0.)
        then wartosc_dokladna 0.
    else match (is_connected a, is_connected b) with
    (* a i b spojne *)
        | (true, true) -> wartosc_od_do
            (minimum
                (min_wartosc a *. min_wartosc b) (min_wartosc a *. max_wartosc b)
                (max_wartosc a *. min_wartosc b) (max_wartosc a *. max_wartosc b))
            (maksimum
                (min_wartosc a *. min_wartosc b) (min_wartosc a *. max_wartosc b)
                (max_wartosc a *. min_wartosc b) (max_wartosc a *. max_wartosc b))
    (* a spojne, b niespojne *)
        | (true, false) -> union
            (razy a (wartosc_od_do b.greater_than infinity))
            (razy a (wartosc_od_do neg_infinity b.less_than))
    (* a niespojne, b spojne *)
        | (false, true) -> razy b a
    (* a i b niespojne *)
        | (false, false) -> union
            (razy (wartosc_od_do neg_infinity a.less_than) b)
            (razy (wartosc_od_do a.greater_than infinity) b)

(* przeciwna wartosc; *)
(* in_wartosc w x <=> in_wartosc (additive_inverse w) (-x) *)
let additive_inverse w =
    razy w (wartosc_dokladna (-1.))

(* x - y = x + (-y) *)
let minus a b =
    plus a (additive_inverse b)

(* czy 0 nalezy do wnetrza w *)
let interior_includes_zero w =
    (w.greater_than <> 0.) && (w.less_than <> 0.) && (in_wartosc w 0.)

(* odwrotna wartosc; *)
(* in_wartosc w x <=> in_wartosc (multiplicative_inverse w) (1./.x) *)
let rec multiplicative_inverse w =
    if is_nan w || w = (wartosc_dokladna 0.) then wartosc_dokladna nan
    else match (interior_includes_zero w, is_connected w) with
    (* spojny bez zera *)
        | (false, true) -> let max_wartosc_w = zero_to_neg_zero (max_wartosc w)
            and min_wartosc_w = neg_zero_to_zero (min_wartosc w)
            in wartosc_od_do
                (min (1. /. max_wartosc_w) (1. /. min_wartosc_w))
                (max (1. /. max_wartosc_w) (1. /. min_wartosc_w))
    (* niespojny bez zera *)
        | (false, false) -> let w_less_than = zero_to_neg_zero (w.less_than)
            and w_greater_than = neg_zero_to_zero (w.greater_than)
            in wartosc_od_do
                (min (1. /. w_less_than) (1. /. w_greater_than))
                (max (1. /. w_less_than) (1. /. w_greater_than))
    (* spojny z zerem *)
        | (true, true) -> union
            (multiplicative_inverse (wartosc_od_do (min_wartosc w) 0.))
            (multiplicative_inverse (wartosc_od_do 0. (max_wartosc w)))
    (* niespojny z zerem *)
        | (true, false) -> union
            (multiplicative_inverse (wartosc_od_do neg_infinity w.less_than))
            (multiplicative_inverse (wartosc_od_do w.greater_than infinity))

(* x / y = x * (1/y) *)
let podzielic a b =
    razy a (multiplicative_inverse b)


(*****************************************************************************)

(* testy *)

(*
open Arytmetyka;;

let is_nan x = compare x nan = 0;;

let a = wartosc_od_do (-1.) 1.            (* <-1, 1> *)
let b = wartosc_dokladna (-1.)            (* <-1, -1> *)
let c = podzielic b a                     (* (-inf -1> U <1 inf) *)
let d = plus c a                          (* (-inf, inf) *)
let e = wartosc_dokladna 0.               (* <0, 0> *)
let f = razy c e                          (* <0, 0> *)
let g = razy d e                          (* <0, 0> *)
let h = wartosc_dokladnosc (-10.) 50.     (* <-15, -5> *)
let i = podzielic h e                     (* nan, przedzial pusty*)
let j = wartosc_od_do (-6.) 5.            (* <-6, 5> *)
let k = razy j j                          (* <-30, 36> *)
let l = plus a b                          (* <-2, 0> *)
let m = razy b l                          (* <0, 2> *)
let n = podzielic l l                     (* <0, inf) *)
let o = podzielic l m                     (* (-inf, 0) *)
let p = razy o a                          (* (-inf, inf) *)
let q = plus n o                          (* (-inf, inf) *)
let r = minus n n                         (* (-inf, inf) *)
let s = wartosc_dokladnosc (-0.0001) 100. (* <-0.0002, 0> *)
let t = razy n s;;                        (* (-inf, 0) *)

assert ((min_wartosc c, max_wartosc c) = (neg_infinity, infinity));
assert (is_nan (sr_wartosc c) );
assert (not (in_wartosc c 0.));
assert ((in_wartosc c (-1.)) && (in_wartosc c (-100000.)) && (in_wartosc c 1.) && (in_wartosc c 100000.));
assert ((in_wartosc d 0.) && (in_wartosc d (-1.)) && (in_wartosc d (-100000.)) && (in_wartosc d 1.) && (in_wartosc d 100000.));
assert ((min_wartosc f, max_wartosc f, sr_wartosc f) = (0., 0., 0.));
assert ((min_wartosc g, max_wartosc g, sr_wartosc g) = (0., 0., 0.));
assert ((min_wartosc h, max_wartosc h, sr_wartosc h) = (-15., -5., -10.));
assert (is_nan (min_wartosc i) && is_nan (sr_wartosc i) && is_nan (max_wartosc i));
assert ((min_wartosc k, max_wartosc k, sr_wartosc k) = (-30., 36., 3.));
assert ((min_wartosc n, max_wartosc n, sr_wartosc n) = (0., infinity, infinity));
assert ((min_wartosc o, max_wartosc o, sr_wartosc o) = (neg_infinity, 0., neg_infinity));
assert ((min_wartosc p, max_wartosc p, is_nan (sr_wartosc p)) = (neg_infinity, infinity, true));
assert ((min_wartosc q, max_wartosc q, is_nan (sr_wartosc q)) = (neg_infinity, infinity, true));
assert ((min_wartosc r, max_wartosc r, is_nan (sr_wartosc r)) = (neg_infinity, infinity, true));
assert ((min_wartosc t, max_wartosc t, sr_wartosc t) = (neg_infinity, 0., neg_infinity));;

let a = wartosc_od_do neg_infinity infinity
let c = plus a a
let d = razy a a
let e = podzielic a a
let f = minus a a;;
assert ((min_wartosc c, max_wartosc c, is_nan (sr_wartosc c)) = (neg_infinity, infinity, true));
assert ((min_wartosc d, max_wartosc d, is_nan (sr_wartosc d)) = (neg_infinity, infinity, true));
assert ((min_wartosc e, max_wartosc e, is_nan (sr_wartosc e)) = (neg_infinity, infinity, true));
assert ((min_wartosc d, max_wartosc d, is_nan (sr_wartosc d)) = (neg_infinity, infinity, true));;

let a = wartosc_od_do 0. infinity
let b = wartosc_dokladna 0.
let c = podzielic a b
let d = podzielic b b;;
assert ((is_nan(min_wartosc c), is_nan(max_wartosc c), is_nan (sr_wartosc c)) = (true, true, true));
assert ((is_nan(min_wartosc d), is_nan(max_wartosc d), is_nan (sr_wartosc d)) = (true, true, true));;

let a = wartosc_od_do (-10.) 10.
let b = wartosc_od_do (-1.) 1000.
let c = podzielic a b;;
assert ((min_wartosc c, max_wartosc c, is_nan (sr_wartosc c)) = (neg_infinity, infinity, true));;

let a = wartosc_od_do (-1.0) 1.0
let b = wartosc_dokladna 1.0
let c = podzielic b a
let d = wartosc_dokladna 3.0
let e = plus c d (* e = (-inf, 2> U <4 inf) *)
let f = podzielic b e (* f = (-inf, 1/4> U <1/2, inf) *)
let g = podzielic d a (* g = (-inf, -3> U <3, inf) *)
let h = podzielic g f (*h = (-inf, inf *)
let i = plus f g (*i = (-inf, inf) *);;

assert ((in_wartosc f 0.25, in_wartosc f 0.26, in_wartosc f 0.49, in_wartosc f 0.50)=(true, false, false, true));
assert ((min_wartosc h, max_wartosc h, is_nan (sr_wartosc h), in_wartosc h 0.) = (neg_infinity, infinity, true, true));
assert ((min_wartosc h, max_wartosc h, is_nan (sr_wartosc h), in_wartosc h 0.3) = (neg_infinity, infinity, true, true));;

let jed = wartosc_dokladna 1.
let zero = wartosc_dokladna 0.;;
assert ((sr_wartosc zero, max_wartosc zero, min_wartosc zero) = (0.,0.,0.));;

let a = wartosc_od_do 0. 1. (* <0,1> *)
let b = podzielic a a (* <0, inf)*)
let c = razy b zero;; (* <0,0> *)
assert ((sr_wartosc c, max_wartosc c, min_wartosc c) = (0.,0.,0.));;

let a = podzielic jed zero;; (* nan *)
assert (is_nan (min_wartosc a));
assert (is_nan (max_wartosc a));
assert (is_nan (sr_wartosc a));;

let a = wartosc_dokladnosc 1. 110.;; (* <-0.1, 2.1> *)
assert (in_wartosc a (-.0.1));
assert (in_wartosc a (2.1));;

let a = wartosc_od_do (-.3.) 0.  (* <-3.0, 0.0> *)
let b = wartosc_od_do 0. 1.      (* <-0.0, 1.0> *)
let c = podzielic a b;;          (* (-inf, 0> *)
assert (max_wartosc c = 0.);
assert (min_wartosc c = neg_infinity);
assert (sr_wartosc c = neg_infinity);;

let a = wartosc_od_do 1. 4.     (* <1.0, 4.0> *)
let b = wartosc_od_do (-.2.) 3. (* <-2.0, 3.0> *)
let c = podzielic a b           (* (-inf, -1/2> U <1/3, inf) *)
let d = podzielic c b           (* (-inf, -1/6> U <1/9, inf) *)
let e = plus d jed              (* (-inf, 5/6> U <10/9, inf) *)
let f = sr_wartosc (podzielic jed (wartosc_dokladna 9.));; (* 1/9 *)
assert (is_nan (sr_wartosc d));
assert (in_wartosc d 0.12);
assert (not (in_wartosc d 0.));
assert (not (in_wartosc d (-0.125)));
assert (in_wartosc d f);
assert (not (in_wartosc e 1.));;

let _ = print_endline "ok :)";;

*)
