open ReM
open Dst
open Parser_plaf.Ast
open Parser_plaf.Parser

(* Alice Agnoletto - CS 496 HW 5 
   I pledge my honor that I have abided by the Stevens Honor System*)

       
let rec chk_expr : expr -> texpr tea_result = function 
  | Int _n -> return IntType
  | Var id -> apply_tenv id
  | IsZero(e) ->
    chk_expr e >>= fun t ->
    if t=IntType
    then return BoolType
    else error "isZero: expected argument of type int"
  | Add(e1,e2) | Sub(e1,e2) | Mul(e1,e2)| Div(e1,e2) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    if (t1=IntType && t2=IntType)
    then return IntType
    else error "arith: arguments must be ints"
  | ITE(e1,e2,e3) ->
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    chk_expr e3 >>= fun t3 ->
    if (t1=BoolType && t2=t3)
    then return t2
    else error "ITE: condition not boolean or types of then and else do not match"
  | Let(id,e,body) ->
    chk_expr e >>= fun t ->
    extend_tenv id t >>+
    chk_expr body
  | Proc(var,Some t1,e) ->
    extend_tenv var t1 >>+
    chk_expr e >>= fun t2 ->
    return @@ FuncType(t1,t2)
  | Proc(_var,None,_e) ->
    error "proc: type declaration missing"
  | App(e1,e2) ->
    chk_expr e1 >>=
    pair_of_funcType "app: " >>= fun (t1,t2) ->
    chk_expr e2 >>= fun t3 ->
    if t1=t3
    then return t2
    else error "app: type of argument incorrect"
  | Letrec([(_id,_param,None,_,_body)],_target) | Letrec([(_id,_param,_,None,_body)],_target) ->
    error "letrec: type declaration missing"
  | Letrec([(id,param,Some tParam,Some tRes,body)],target) ->
    extend_tenv id (FuncType(tParam,tRes)) >>+
    (extend_tenv param tParam >>+
     chk_expr body >>= fun t ->
     if t=tRes 
     then chk_expr target
     else error
         "LetRec: Type of recursive function does not match declaration")
  | NewRef (e) -> 
    chk_expr e >>= fun t ->
    return (RefType t)
  | DeRef (e) -> 
    chk_expr e >>= fun t ->
    ( match t with 
      | RefType ref -> return ref
      | _ -> error "deref: must be a reference"
    )
  | SetRef (e1, e2) -> 
    chk_expr e1 >>= fun t1 ->
    ( match t1 with 
      | RefType ref -> 
        chk_expr e2 >>= fun t2 ->
        (if (ref=t2)
        then return UnitType 
        else error " setref: type missmatch ")
      | _ -> error "setref: Expected a reference type")
  | BeginEnd([]) -> 
    return UnitType
  | BeginEnd(es) ->
    let result =  (be_helper es) in result
  | EmptyList(t) -> 
    (match t with 
    | None -> error "EmptyList: error creeating empty list "
    | Some tr -> return (ListType tr))
  | Cons (e1, e2) -> 
    chk_expr e1 >>= fun t1 ->
    chk_expr e2 >>= fun t2 ->
    (match t2 with 
    | ListType t -> 
      if t=t1 
      then return (ListType t)
      else error "cons: type of head and tail do not match"
    | _ -> error "cons: type of arguments incorrect")
  | IsEmpty (e) -> 
    chk_expr e >>= fun t ->
      (match t with 
      | ListType _ -> return BoolType
      | TreeType _ -> return BoolType
      | _ -> error "IsEmpty: expected ListType or TreeType" )
  | Hd (e) ->
    chk_expr e >>= fun t ->
    (match t with 
    | ListType t1 -> return t1
    | _ -> error "Hd: must be ListType"
    )
  | Tl (e) -> 
    chk_expr e >>= fun t ->
    (match t with 
    | ListType _ -> return t
    | _ -> error "Hd: must be ListType"
    )
  | Debug(_e) ->
    string_of_tenv >>= fun str ->
    print_endline str;
    error "Debug: reached breakpoint" 
  | EmptyTree (t) -> 
    (match t with 
    | None -> error "EmptyList: error creating empty tree "
    | Some t -> return (TreeType t))
  | Node (de ,le ,re) -> 
    chk_expr de >>= fun t1 -> (* is IntType*)
    chk_expr le >>= fun l -> (* is (TreeType IntType)*)
    chk_expr re >>= fun r -> (* is (TreeType IntType)*)
    (match l,r with
      | TreeType t2, TreeType t3 -> 
        if (t2=t3)
        then 
          if (t1=t3)
          then return (TreeType t1)
          else error "Node: type missmatch"
        else error "Node: type missmatch"
      | _ -> error "Node: must be TreeType"
      )
   | CaseT (target, emptycase, id1 , id2 , id3 , nodecase ) -> 
      chk_expr target >>= fun t1 ->
      ( match t1 with 
      | TreeType t -> 
        chk_expr emptycase >>= fun t2 ->
          (if t1=t2 
          then extend_tenv id1 t >>+ 
          extend_tenv id2 (TreeType t) >>+ 
          extend_tenv id3 (TreeType t) >>+ 
          chk_expr nodecase
          else chk_expr emptycase )
      | _ -> error "CaseT: target must be TreeType") 
  | _ -> failwith "chk_expr: implement"    
and
  chk_prog (AProg(_,e)) =
  chk_expr e
and 
be_helper l = 
  (match l with 
    | [e] -> chk_expr e >>= fun t1 -> return t1
    | _::t -> (be_helper t) 
    | _ -> failwith "BeginEnd: must be a list" )


(* Type-check an expression *)
let chk (e:string) : texpr result =
  let c = e |> parse |> chk_prog
  in run_teac c

let chkpp (e:string) : string result =
  let c = e |> parse |> chk_prog
  in run_teac (c >>= fun t -> return @@ string_of_texpr t)




