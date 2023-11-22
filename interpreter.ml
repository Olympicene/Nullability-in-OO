open List

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

type cldecl = { clname : ident; super : ident; fields : (typ * ident) list; methods : mdecl list }

(* contexts *)
type ty_entry = Ty of typ (* Entries in the type context can either be the types of variables, or the definitions of classes. *)
              | Class of cldecl

type context = ident -> ty_entry option
let empty_context = fun x -> None
let context_lookup (gamma : context) (x : ident) : ty_entry option = gamma x
let context_update (gamma : context) (x : ident) (e : ty_entry) = fun y -> if y = x then Some e else gamma y

let lookup_var (gamma : context) (x : ident) : typ option =
  match context_lookup gamma x with Some (Ty t) -> Some t | _ -> None
let lookup_class (gamma : context) (x : ident) : cldecl option =
  match context_lookup gamma x with Some (Class cd) -> Some cd | _ -> None
let update_var (gamma : context) (x : ident) (t : typ) : context = context_update gamma x (Ty t)
let update_class (gamma : context) (x : ident) (cl : cldecl) : context = context_update gamma x (Class cl)

(* field and method lookup *)
let rec fields (ct : context) (cl : ident) : (typ * ident) list =
  if cl = "Object" then [] else
    match lookup_class ct cl with
    | Some cd -> fields ct cd.super @ cd.fields
    | _ -> []

let types_of_params (params : (typ * ident) list) : typ list =
  List.map fst params

let names_of_params (params : (typ * ident) list) : ident list =
    List.map snd params
  
let field_type_aux (l : (typ * ident) list) (f : ident) : typ option =
  match List.find_opt (fun (_, n) -> n = f) l with
  | Some (t, _) -> Some t
  | _ -> None

let field_type (ct : context) (cl : ident) (f : ident) : typ option =
  field_type_aux (rev (fields ct cl)) f

let rec methods (ct : context) (cl : ident) : mdecl list =
  if cl = "Object" then [] else
    match lookup_class ct cl with
    | Some cd -> methods ct cd.super @ cd.methods
    | _ -> []

let lookup_method_aux (l : mdecl list) (m : ident) : mdecl option =
  find_opt (fun d -> d.mname = m) l

let lookup_method (ct : context) (cl : ident) (m : ident) : mdecl option =
  lookup_method_aux (rev (methods ct cl)) m

(* semantics *)
type reference = int
type value = IntVal of int | RefVal of reference | NullRefVal

(* environment implementation *)
type env = ident -> value option
let empty_env = fun x -> None
let lookup (r : env) (x : ident) : value option = r x
let update (r : env) (x : ident) (e : value) : env = fun y -> if y = x then Some e else r y

let rec add_args (r : env) (li : ident list) (lv : value list) : env =
  match li, lv with
  | i :: irest, v :: vrest -> add_args (update r i v) irest vrest
  | _, _ -> r
(* end environment implementation *)

(* store implementation *)
type obj = ObjVal of ident (* class name *) * env (* field values *)
type store = (reference -> obj option) * int
let empty_store : store = ((fun x -> None), 0)
let store_lookup (s : store) (x : reference) : obj option = (fst s) x
let store_update (s : store) (x : reference) (o : obj) : store = let (r, n) = s in ((fun y -> if y = x then Some o else r y), n)
let alloc (s : store) (o : obj) : store * reference = let (r, n) = s in (((fun y -> if y = n then Some o else r y), n + 1), n)
(* end store implementation *)

(* Semantics *)
let rec eval_exp (e : exp) (r : env) (s : store) : value option =
  match e with
  | Var x -> lookup r x
  | Num i -> Some (IntVal i)
  | Add (e1, e2) -> (match eval_exp e1 r s, eval_exp e2 r s with
                     | Some (IntVal i1), Some (IntVal i2) -> Some (IntVal (i1 + i2))
                     | _, _ -> None)
  | Mul (e1, e2) -> (match eval_exp e1 r s, eval_exp e2 r s with
                     | Some (IntVal i1), Some (IntVal i2) -> Some (IntVal (i1 * i2))
                     | _, _ -> None)
  | GetField (e, f) -> (match eval_exp e r s with
                        | Some (RefVal p) -> (match store_lookup s p with
                                              | Some (ObjVal (_, fs)) -> lookup fs f
                                              | _ -> None)
                        | _ -> None)
  | NullReference -> Some NullRefVal

let rec eval_exps (es : exp list) (r : env) (s : store) : value list option =
  match es with
  | [] -> Some []
  | e :: rest -> (match eval_exp e r s, eval_exps rest r s with
                  | Some v, Some vs -> Some (v :: vs)
                  | _, _ -> None)

type stack = (env * ident) list

type config = cmd * stack * env * store

let rec step_cmd (gamma : context) (con : config) : config option =
  let (c, k, r, s) = con in
  match c with
  | Assign (x, e) -> (match eval_exp e r s with
                      | Some v -> Some (Skip, k, update r x v, s)
                      | None -> None)
  | Seq (Skip, c2) -> Some (c2, k, r, s)
  | Seq (c1, c2) -> (match step_cmd gamma (c1, k, r, s) with
                     | Some (c1', k', r', s') -> Some (Seq (c1', c2), k', r', s')
                     | None -> None)
  | Skip -> None
  | New (x, cl, es) -> (match eval_exps es r s with
                       | Some vs -> let (s', p) = alloc s (ObjVal (cl, add_args empty_env (names_of_params (fields gamma cl)) vs)) in
                                      Some (Skip, k, update r x (RefVal p), s')
                       | _ -> None)
  | Invoke (x, e, m, es) -> (match eval_exp e r s, eval_exps es r s with
                             | Some (RefVal p), Some vs ->
                                 (match store_lookup s p with
                                  | Some (ObjVal (cl, _)) ->
                                      (match lookup_method gamma cl m with
                                       | Some md -> Some (md.body, (r, x) :: k, update (add_args r (names_of_params md.params) vs) "this" (RefVal p), s)
                                       | _ -> None)
                                  | _ -> None)
                             | _, _ -> None)
  | Return e -> (match eval_exp e r s, k with
                 | Some v, (r', x) :: k' -> Some (Skip, k', update r' x v, s)
                 | _, _ -> None)

let rec run_config gamma (con : config) : config =
  match step_cmd gamma con with
  | Some con' -> run_config gamma con'
  | None -> con

let run_prog gamma (c : cmd) =
  run_config gamma (c, [], empty_env, empty_store)

(* test cases *)
let ct0 = context_update (context_update empty_context
    "Shape" (Class {clname = "Shape"; super = "Object"; fields = [(IntTy, "id")];
          methods = [{ret = IntTy; mname = "area"; params = []; body = Return (Num 0)}]}))
    "Square" (Class {clname = "Square"; super = "Shape"; fields = [(IntTy, "side")];
               methods = [{ret = IntTy; mname = "area"; params = [];
                    body = Seq (Assign ("x", GetField (Var "this", "side")),
                       Return (Add (Var "x", Var "x")))}]})

let fields0 = update empty_env "id" (IntVal 2)
let (store0, ref0) = alloc empty_store (ObjVal ("Shape", fields0))
let env0 = update empty_env "s" (RefVal ref0)

let exp2 : exp = GetField (Var "s", "id")
  
let cmd3 : cmd =
  Seq (New ("s", "Square", [Num 0; Num 2]),
       (* s = new Square(0, 2); *)
       Assign ("y", Add (GetField (Var "s", "side"), Num 1)))
       (* y = s.side + 1; *)
  
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
let field_test1 = eval_exp exp2 env0 store0
  
let new_test1 = run_prog ct0 cmd3
  
let invoke_test1 = run_prog ct0 cmd4
  
let invoke_test2 = run_prog ct0 cmd5
