(* Alice Agnoletto
   I pledge my honor that I have abided by the stevens honor system. *)

open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds
    
(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | EmptyTree(_t) -> return (TreeVal(Empty))
  | Node(e1, e2, e3) ->
    eval_expr e1 >>= fun data ->
    eval_expr e2 >>=
    tree_of_treeVal >>= fun t2 ->
    eval_expr e3 >>=
    tree_of_treeVal >>= fun t3 ->
    return ( TreeVal (Node(data, t2, t3)))
  | IsEmpty(e) ->
    eval_expr e >>=
    tree_of_treeVal >>= fun t ->
      if t=Empty
        then return (BoolVal true)
    else
      return (BoolVal false)
  | Record(fs) -> 
      eval_exprs (List.map snd (List.map snd fs)) >>= fun l ->
      let rec has_duplicates = function
    | [] -> false
    | h::t -> if List.mem h t then true else has_duplicates t
    in if has_duplicates (List.map fst fs)
    then error "Record: duplicate fields"
    else return (RecordVal (List.combine (List.map fst fs) l))
  | Proj(e, id) -> eval_expr e >>=
    record_of_recordVal >>= fun record ->
    let ids = List.map fst record in
  if List.mem id ids
    then return (List.assoc id record)
  else error "Proj: Field not found"
  | CaseT(e1, e2, id1, id2, id3, e3) ->
    eval_expr e1 >>= tree_of_treeVal >>=
    fun t1 ->
      (match t1 with
      | Empty -> eval_expr e2
      | Node(data, l, r) -> 
        extend_env id1 data >>+
        extend_env id2 (TreeVal l) >>+
        extend_env id3 (TreeVal r) >>+
        eval_expr e3
      | _ -> error "Invalid")
  | _ -> failwith "Not implemented yet!" 
  and
    eval_exprs : expr list -> ( exp_val list ) ea_result =
    fun es ->
    match es with
    | [] -> return []
    | h :: t -> eval_expr h >>= fun i ->
    eval_exprs t >>= fun l ->
    return ( i :: l )
  


(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e


(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c
  


