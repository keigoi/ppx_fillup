
let concat (_: < .. >) (_: < .. >) : < .. > = 
  failwith "Impossible: This must not be called"

(* <a:unit; b:unit> *)
let ab = 
  concat 
    (object method a = () end) 
    (object method b = () end)
(* 
let ab =
  let obj1 = object method a = () end
  and obj2 = object method b = () end in
  object method a = obj1#a method b = obj2#b end 
*)
    
let duck =
  object
    method quack = "quack"
  end

let cow =
  object
    method moo = "moo"
  end

(* <moo:string; quack:string> *)
let duckcow =
  concat duck cow
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
let intbool = concat int bool
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
