(* syntax *)
type ident = string

type typ = IntTy | NonNullClassTy of ident | NullableClassTy of ident | NullReferenceTy (* The kinds of types a variable can have. *)
type exp = Num of int | Add of exp * exp | Mul of exp * exp | Var of ident
         | GetField of exp * ident | NullReference

type cmd = Assign of ident * exp | Seq of cmd * cmd | Skip
         | New of ident * ident * exp list
         | Invoke of ident * exp * ident * exp list | Return of exp
         | IfNotNull of ident * cmd


type mdecl = { ret : typ; mname : ident; params : (typ * ident) list; body : cmd }

type cdecl = { cname : ident; super : ident; fields : (typ * ident) list; methods : mdecl list }

(* contexts *)
type ty_entry = Ty of typ (* Entries in the type context can either be the types of variables, or the definitions of classes. *)
              | Class of cdecl

type context = ident -> ty_entry option
let empty_context = fun x -> None
let lookup (gamma : context) (x : ident) : ty_entry option = gamma x
let update (gamma : context) (x : ident) (e : ty_entry) = fun y -> if y = x then Some e else gamma y

let lookup_var (gamma : context) (x : ident) : typ option =
  match lookup gamma x with Some (Ty t) -> Some t | _ -> None
let lookup_class (gamma : context) (x : ident) : cdecl option =
  match lookup gamma x with Some (Class cd) -> Some cd | _ -> None
let update_var (gamma : context) (x : ident) (t : typ) : context = update gamma x (Ty t)
let update_class (gamma : context) (x : ident) (c : cdecl) : context = update gamma x (Class c)

(* field and method lookup *)
let rec fields (ct : context) (c : ident) : (typ * ident) list =
  if c = "Object" then [] else
    match lookup_class ct c with
    | Some cd -> fields ct cd.super @ cd.fields
    | _ -> []

let types_of_params (params : (typ * ident) list) : typ list =
  List.map fst params

let field_type_aux (l : (typ * ident) list) (f : ident) : typ option =
  match List.find_opt (fun (_, n) -> n = f) l with
  | Some (t, _) -> Some t
  | _ -> None

let field_type (ct : context) (c : ident) (f : ident) : typ option =
  field_type_aux (List.rev (fields ct c)) f

let rec methods (ct : context) (c : ident) : mdecl list =
  if c = "Object" then [] else
    match lookup_class ct c with
    | Some cd -> methods ct cd.super @ cd.methods
    | _ -> []

let lookup_method_aux (l : mdecl list) (m : ident) : mdecl option =
  List.find_opt (fun d -> d.mname = m) l

let lookup_method (ct : context) (c : ident) (m : ident) : mdecl option =
  lookup_method_aux (List.rev (methods ct c)) m

let rec supers (ct : context) (c : ident) : ident list = (* Answer to problem 1 *)
  match lookup_class ct c with
  | None -> []
  | Some cd when cd.super = "Object" -> ["Object"]
  | Some cd -> cd.super::(supers ct cd.super) ;;

let subtype (ct : context) (t1 : typ) (t2 : typ) : bool = (t1 = t2) ||
  match t1, t2 with
  | NonNullClassTy c1, NonNullClassTy c2 
  | NonNullClassTy c1, NullableClassTy c2 (* All non-nullable class types are subtypes of their corresponding nullable types, but the reverse is not true. *)
  | NullableClassTy c1, NullableClassTy c2 
    -> c1 = c2 || List.exists ((=) c2) (supers ct c1) 
                                              (* Having to check for identical types here again is a bit ugly. Is there an obvious better way? *)
  | NullReferenceTy, NullableClassTy _ -> true
  | _, _ -> false
    
let rec type_of (gamma : context) (e : exp) : typ option =
  match e with
  | Num i -> Some IntTy
  | Add (e1, e2) | Mul (e1, e2) ->
      (match type_of gamma e1, type_of gamma e2 with
       | Some IntTy, Some IntTy -> Some IntTy
       | _, _ -> None)
  | Var x -> lookup_var gamma x  
  | GetField (obj, f) -> (* Answer to problem 2 *)
      (match type_of gamma obj with 
       | Some NonNullClassTy c -> field_type gamma c f 
       | _ -> None)
  | NullReference -> Some NullReferenceTy
;;

let typecheck (gamma : context) (e : exp) (t : typ) : bool =
  match type_of gamma e with
  | Some t1 -> subtype gamma t1 t
  | None -> false

let rec typecheck_list (gamma : context) (es : exp list) (ts : typ list) : bool =
  List.for_all2 (typecheck gamma) es ts
  
let rec typecheck_cmd (gamma : context) (c : cmd) : bool =
  match c with
  | Assign (i, e) ->
      (match lookup_var gamma i with
       | Some t -> typecheck gamma e t
       | None -> false)
  | Seq (c1, c2) -> typecheck_cmd gamma c1 && typecheck_cmd gamma c2
  | Skip -> true
  | New (target, c, cargs) ->
      (match lookup_var gamma target with
       | Some targetTyp -> (subtype gamma (NonNullClassTy c) targetTyp) && (fields gamma c |> types_of_params |> typecheck_list gamma cargs)
       | _ -> false)
  | Invoke (varname, obj, m, arglist) -> (match type_of gamma obj with (* Problem 4 solution here, though I am not a grad student. *)
                                            | Some NonNullClassTy c -> (match lookup_method gamma c m, lookup_var gamma varname with 
                                                                | Some mdec, Some ty -> mdec.params |> types_of_params |> typecheck_list gamma arglist 
                                                                  && (subtype gamma mdec.ret ty)
                                                                | _, _ -> false)
                                            | _ -> false )
  (* problem 4 (grad only) *)
  | Return e ->
      (match lookup_var gamma "__ret" with
       | Some t -> typecheck gamma e t
       | None -> false)

(* test cases *)  
let ct0 = update (update empty_context
    "Shape" (Class {cname = "Shape"; super = "Object"; fields = [(IntTy, "id")];
          methods = [{ret = IntTy; mname = "area"; params = []; body = Return (Num 0)}]}))
    "Square" (Class {cname = "Square"; super = "Shape"; fields = [(IntTy, "side")];
               methods = [{ret = IntTy; mname = "area"; params = [];
                    body = Seq (Assign ("x", GetField (Var "this", "side")),
                       Return (Add (Var "x", Var "x")))}]})

let gamma0 : context = update_var (update_var (update_var ct0 "s" (NonNullClassTy "Square")) "x" IntTy) "y" IntTy

let gamma1 : context = update_var (update_var (update_var ct0 "s" (NonNullClassTy "Shape")) "x" IntTy) "y" IntTy

let gamma2 : context = update_var (update_var (update_var (update_var ct0 "s2" (NonNullClassTy "Square")) "s1" (NonNullClassTy "Shape")) "x" IntTy) "y" IntTy


let exp2 : exp = GetField (Var "s", "id")
  
let cmd3 : cmd =
  Seq (New ("s", "Square", [Num 0; Num 2]),
       (* s = new Square(0, 2); *)
       Assign ("y", Add (GetField (Var "s", "side"), Num 1)))
       (* y = s.side + 1; *)
  
(* for the grad student problem *)
let cmd4 : cmd =
  Seq (New ("s", "Shape", [Num 2]),
       (* s = new Shape(2); *)
       Invoke ("x", Var "s", "area", []))
       (* x = s.area(); *)
  
let cmd5 : cmd =
  Seq (New ("s", "Square", [Num 0; Num 2]),
       (* s = new Square(0, 2); *)
  Seq (Assign ("y", Add (GetField (Var "s", "side"), Num 1)),
       (* y = s.side + 1; *)
       Invoke ("x", Var "s", "area", [])))
       (* x = s.area(); *)

(* run the tests *)
let supers_test1 = assert (subtype ct0 (NonNullClassTy "Square") (NonNullClassTy "Object") = true) (* should return true *)

let supers_test2 = assert (subtype ct0 (NonNullClassTy "Object") (NonNullClassTy "Square") = false) (* should return false *)

let field_test1 = assert ((type_of gamma0 exp2 = Some IntTy) = true) (* should return true *)
  
let new_test1 = assert (typecheck_cmd gamma0 cmd3 = true) (* should return true *)
  
let invoke_test1 = assert (typecheck_cmd gamma1 cmd4 = true)(* should return true *)
  
let invoke_test2 = assert (typecheck_cmd gamma0 cmd5 = true) (* should return true *)

let gamma3 : context = update_var gamma2 "s3" (NonNullClassTy "Object")

(* More Test Cases *)

let ctc = update (update empty_context
    "Point" (Class {cname = "Point"; super = "Object"; fields = [(IntTy, "x"); (IntTy, "y")];
          methods = [{ret = IntTy; mname = "getx"; params = []; body = Return (GetField (Var "this", "x"))}]}))
    "Circle" (Class {cname = "Circle"; super = "Shape"; fields = [(NonNullClassTy "Point", "center")];
               methods = []})

let gammac = update_var ctc "circle" (NonNullClassTy "Circle")

let testc : exp = (GetField (GetField (Var "circle", "center"), "x"))
let resc = assert ((type_of gammac testc = Some IntTy) = true)
(* bool = true *)


let gamma3 : context = update_var gamma2 "s3" (NonNullClassTy "Object")

let test6 : exp = (GetField (Var "s1", "side"))
let res6 = assert ((type_of gamma2 test6 = Some IntTy) = false)
(* bool = false *)

let test7 : exp = (GetField (Var "s2", "side"))
let res7 = assert ((type_of gamma2 test7 = Some IntTy) = true)
(* bool = true *)

let test8 : exp = (GetField (Var "s2", "id"))
let res8 = assert ((type_of gamma0 test8 = Some IntTy) = false)
(* bool = false *)

let test9 : exp = (GetField (Var "s2", "id"))
let res9 = assert ((type_of gamma2 test9 = Some (NonNullClassTy "s2")) = false)
(* bool = false *)

let test10 : cmd = Assign ("s1", Var "x")
let res10 = assert (typecheck_cmd gamma2 test10 = false)
(* bool = false *)

let test11 : cmd = Assign ("x", Var "s")
let res11 = assert (typecheck_cmd gamma0 test11 = false)
(* bool = false *)

let test12 : cmd = Assign ("x", Var "y")
let res12 = assert (typecheck_cmd gamma3 test12 = true)
(* bool = true *)

let test13 : cmd = Assign ("s2", Var "s1")
let res13 = assert (typecheck_cmd gamma3 test13 = false)
(* bool = false *)

let test14 : cmd = Assign ("s3", Var "s1")
let res14 = assert (typecheck_cmd gamma3 test14 = true)
(* bool = true *)

let test15 : cmd =
 Seq (New ("s", "Square", [Num 0; Num 2]),
       (* s = new Square(0, 2); *)
       Invoke ("x", Var "s", "area", []))
       (* s.side = s.area(); *)
let res15 = assert (typecheck_cmd gamma1 test15 = true)
(* bool = true *)

let test16 : cmd =
 Seq (New ("s", "Square", [Num 0; Num 2]),
       (* s = new Square(0, 2); *)
       Invoke ("s", Var "s", "area", []))
       (* s = s.area(); *)
let res16 = assert (typecheck_cmd gamma1 test16 = false)
(* bool = false *)

(* New tests begin here: *)
(* Basic Nullability tests: *)
let ctn0 = update ct0 "ShapeNode" (Class {cname = "ShapeNode"; super = "Object"; fields = [(NonNullClassTy "Shape", "value"); 
        (NullableClassTy "ShapeNode", "next")]; methods = []})
let ctn1 = update ctn0 "ListOfShapes" (Class {cname = "ListOfShapes"; super = "Object"; fields = [(NullableClassTy "ShapeNode", "head"); 
        (IntTy, "length")]; methods = [{ret = IntTy; mname = "getSize"; params = [];
        body = Return (GetField (Var "this", "size"))}]})

let gamman0 = update_var (update_var (update_var ctn0 "snode" (NonNullClassTy "ShapeNode")) "snode_null" (NullableClassTy "ShapeNode")) 
              "s0" (NonNullClassTy "Shape")
let testn0 = Seq (New ("s0", "Shape", [Num 2]), New ("snode_null", "ShapeNode", [Var "s0"; NullReference]))
let resn0 = assert (typecheck_cmd gamman0 testn0 = true)