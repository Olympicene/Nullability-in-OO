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