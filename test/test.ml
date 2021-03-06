(* don't make preprocessor warnings as errors *)
[@@@warnerror "-22"]

type 'a show = {show:'a -> string}
[@@typeclass]


module M = struct
  let _str[@instance] = {show=(fun x -> Printf.sprintf "\"%s\"" x)}
  let _int[@instance] = {show=(fun x -> Printf.sprintf "\"%d\"" x)}
  let _pair[@instance] = fun (d1:_ show) (d2:_ show) -> 
    {show=(fun (x,y) -> Printf.sprintf "(%s,%s)" (d1.show x) (d2.show y))}
end
open M

let show (dict:'a show) v = dict.show v

let () =
  print_endline @@ show ## 1
  ;
  print_endline @@ show ## "abc"
  ;
  print_endline @@ show ## (1, "abc")
  (* ;
  List.iter ## [1;2;3] *)
  (* ;
  print_endline @@ show ## (1, true) *)

type t = T of int[@@typeclass]
type u = U of int[@@typeclass]

let inst2[@instance] = T 1
let inst[@instance] = fun (_x:t) -> print_endline "called"; (U 1)

let f (U(x)) y z = x + y + z
let _ = f ## 1 2
let _ = f ## 1 2

(* object concatenation (experimental) *)

type ('lr,'l,'r) disj = {
  concat:'l -> 'r -> 'lr;
  split:'lr -> 'l * 'r;
}
[@@typeclass]
[@@disjoint_objects: 'l * 'r -> 'lr]

let concat disj x y =
  disj.concat x y

(* <a:unit; b:unit> *)
let ab = concat ## (object method a = () end) (object method b = () end)

let abc =
  concat ## ab (object method c = () end)

let abc' =
  concat ## ab (object method c = () end)

let _ =
  concat ## (concat ## (object method a = () end) (object method b = () end)) (object method c = () end)

let aabc = 
  concat ## (object method outer = ab end) (object method outer = object method c = () end end)

let duck =
  object
    method quack = "quack"
  end

let x = 1

let cow =
  object
    method moo = "moo"
  end

(* <moo:string; quack:string> *)
let duckcow =
  concat ## duck cow
(* 
let obj1 = duck
  and obj2 = cow in
  object method quack = obj1#quack method moo = obj2#moo end 
*)

let int =
  object
    method to_int = int_of_string
    method of_int = string_of_int
  end

let bool =
  object
    method to_bool = bool_of_string
    method of_bool = string_of_bool
  end

(* <of_bool: bool -> string; of_int: int -> string; to_bool: string -> bool; to_int: string->int> *)
let intbool = concat ## int bool
(* 
let intbool =
  let obj1 = int
  and obj2 = bool in
  object
    method of_int = obj1#of_int
    method to_int = obj1#to_int
    method of_bool = obj2#of_bool
    method to_bool = obj2#to_bool
  end 
*)

(* still won't work *)
(* 
let na =
  concat duckcow intbool 
==> object type is open < .. > (at the use of duckcow)
*)

(*
let f x y =
  concat x y
==> object type is open < .. > (at the use of x)
*)
