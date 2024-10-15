(* 
    FVPgen: automatically generating rewrite theories and proving Finite Variant Property
    Copyright (C) 2024 Vincent Cheval (University of Oxford).

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>
*)

let rule_computed = ref 0

(* Term module *)

type link = ..

and variable = 
  {
    v_name : string;
    v_id : int;
    mutable v_link : link
  }

and symbol_cat =
  | AC
  | Syntactic

and symbol =
  {
    f_name : string;
    f_id: int;
    f_cat : symbol_cat;
    f_arity : int
  }

and term =
  | Var of variable
  | Func of symbol * term list

type link +=
  | NoLink
  | TLink of term
  | VLink of variable
  | Marked

type subst = (variable * term) list

let hole = Func({f_name = "__";f_id = 0; f_cat = Syntactic;f_arity =0 },[])

let compare_variable v1 v2 = compare v1.v_id v2.v_id

let compare_symbol f1 f2 = compare f1.f_id f2.f_id

let less_symbol f1 f2 = f1.f_id < f2.f_id

let fresh_variable =
  let acc = ref 1 in
  fun () ->
    let r = !acc in
    incr acc;
    { v_name = "x"; v_id = r; v_link = NoLink }

(* Table *)

let symbol_table : (string,symbol) Hashtbl.t = Hashtbl.create 1

let get_symbol str =
  Hashtbl.find symbol_table str

let amin = ref { f_name =""; f_id = 0; f_cat = Syntactic; f_arity = 0}
let fbin = ref { f_name =""; f_id = 0; f_cat = Syntactic; f_arity = 0}
let dummy_context = Func({ f_name ="_"; f_id = 0; f_cat = Syntactic; f_arity = 0},[])

let all_symbols = ref []

let initialise_symbols list_symb = 
  let list_symb' = match list_symb with
    | (str,0,Syntactic)::_ -> list_symb
    | _ -> ("amin",0,Syntactic) :: list_symb
  in

  Printf.printf "Order read: ";
  List.iteri (fun i (str,n,cat) ->
    Printf.printf "%s/%d < " str n;
    let f = { f_name = str; f_id = i+1; f_arity = n; f_cat = cat } in
    Hashtbl.add symbol_table str f;
    all_symbols := f :: !all_symbols
  ) list_symb';

  let i = List.length list_symb' + 1 in

  let f_bin = { f_name = "bin"; f_id = i; f_arity = 2; f_cat = Syntactic } in
  fbin := f_bin;
  Hashtbl.add symbol_table "bin" f_bin;
  all_symbols := f_bin :: !all_symbols;

  let f_name = { f_name = "name"; f_id = i+1; f_arity = 1; f_cat = Syntactic } in
  Hashtbl.add symbol_table "name" f_name;
  all_symbols := f_name :: !all_symbols;

  Printf.printf "bin/2 < name/1\n";

  amin := List.hd (List.rev !all_symbols)

(* Display functions *)

let rec display_list_aux display_item sep = function
  | [] -> ()
  | x::q -> print_string sep; display_item x; display_list_aux display_item sep q

let display_list display_empty display_item sep = function
  | [] -> display_empty ()
  | x::q -> display_item x; display_list_aux display_item sep q

let rec string_of_list_aux string_of_item sep = function
  | [] -> ""
  | x::q -> sep ^ (string_of_item x) ^ (string_of_list_aux string_of_item sep q)

let string_of_list string_of_item sep = function
  | [] -> ""
  | x::q -> (string_of_item x) ^ (string_of_list_aux string_of_item sep q)

let string_of_variable v = Printf.sprintf "X_%d" v.v_id

let rec string_of_term = function
  | Var v -> string_of_variable v
  | Func(f,[]) -> f.f_name
  | Func(f,args) ->
      match f.f_cat with
        | Syntactic -> Printf.sprintf "%s(%s)" f.f_name (string_of_list string_of_term "," args)
        | AC -> Printf.sprintf "(%s)" (string_of_list string_of_term (" "^f.f_name^" ") args)

let string_of_subst subst = 
  if subst = []
  then "Id"
  else 
    "{ " ^
    string_of_list (fun (x,t) ->
      (string_of_variable x) ^ " -> " ^ (string_of_term t)
    ) "; " subst ^
    " }"

(*********************
   Cleanup           
**********************)

let current_bound_vars = ref []

let link v l = 
  current_bound_vars := v :: !current_bound_vars;
  v.v_link <- l

let cleanup () =
  List.iter (fun v -> v.v_link <- NoLink) (!current_bound_vars);
  current_bound_vars := []
 
let auto_cleanup_noreset f = 
  let tmp_bound_vars = !current_bound_vars in

  let rec reset_link l = 
    if tmp_bound_vars == l
    then ()
    else 
      begin match l with 
      | v::q -> 
          v.v_link <- NoLink;
          reset_link q
      | _ -> failwith "Unexpected case"
      end
  in

  try
    let r = f () in
    reset_link !current_bound_vars;
    current_bound_vars := tmp_bound_vars;
    r
  with x ->
    begin
      reset_link !current_bound_vars;
      current_bound_vars := tmp_bound_vars;
      raise x
    end

let auto_cleanup f =
  let tmp_bound_vars = !current_bound_vars in
  current_bound_vars := [];
  try
    let r = f () in
    List.iter (fun v -> v.v_link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    r
  with x ->
    List.iter (fun v -> v.v_link <- NoLink) (!current_bound_vars);
    current_bound_vars := tmp_bound_vars;
    raise x

let auto_cleanup_no_catch f = 
  let tmp_bound_vars = !current_bound_vars in
  current_bound_vars := [];
  let r = f () in
  List.iter (fun v -> v.v_link <- NoLink) (!current_bound_vars);
  current_bound_vars := tmp_bound_vars;
  r

(*********************
   Copy, Refresh         
**********************)

let rec refresh_term = function
  | Var { v_link = VLink v'; _ } -> Var v'
  | Var { v_link = TLink t; _ } -> refresh_term t
  | Var v -> 
      let v' = fresh_variable () in
      link v (VLink v');
      Var v'
  | Func(f,args) -> Func(f,List.map refresh_term args)

let rec copy_term_non_rec = function
  | Var { v_link = TLink t; _ } -> t
  | Var _ as t -> t
  | Func(f,args) -> Func(f,List.map copy_term_non_rec args)

let rec apply_renaming = function
  | Var { v_link = VLink v; _ } -> Var v
  | Var _ as t -> t
  | Func(f,args) -> Func(f,List.map apply_renaming args)

(****)

let apply_subst subst t = 
  auto_cleanup (fun () ->
    List.iter (fun (x,u) -> link x (TLink u)) subst;
    copy_term_non_rec t
  )

let rec occurs v = function
  | Var x -> x == v
  | Func(_,args) -> List.exists (occurs v) args

(* Compute vars(t1) \ vars(t2) *)
let diff_vars t1 t2 = 
  
  let rec go_through_t2 = function
    | Var v when v.v_link = NoLink -> link v (VLink v)
    | Var _ -> ()
    | Func(_,args) -> List.iter go_through_t2 args
  in
  
  let rec go_through_t1 vars = function
    | Var v when v.v_link = NoLink -> 
        vars := v :: !vars
    | Var _ -> () 
    | Func(_,args) -> List.iter (go_through_t1 vars) args
  in

  auto_cleanup (fun () ->
    go_through_t2 t2;
    let vars = ref [] in
    go_through_t1 vars t1;
    !vars
  )

let rec get_variables = function
  | Var ({ v_link = NoLink; _ } as v) -> 
      link v (VLink v)
  | Var _ -> ()
  | Func(_,args) -> List.iter get_variables args


(****)

let rec lexicographic_compare comp_fun list1 list2 = match list1,list2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | t1::q1, t2::q2 ->
      match comp_fun t1 t2 with
      | 0 -> lexicographic_compare comp_fun q1 q2
      | c -> c

let rec compare_term t1 t2 = match t1, t2 with
  | Var v1, Var v2 -> compare v1.v_id v2.v_id
  | Var _, _ -> -1
  | _, Var _ -> 1
  | Func(f1,args1), Func(f2,args2) ->
      match compare f1.f_id f2.f_id with
      | 0 -> lexicographic_compare compare_term args1 args2
      | c -> c

let rec equal t1 t2 = match t1, t2 with
  | Var v1, Var v2 -> v1 == v2
  | Func(f1,args1), Func(f2,args2) when f1 == f2 ->
      List.for_all2 equal args1 args2
  | _ -> false

(* Add [u] in the increasingly sorted list [tlist] *)
let rec sorted_add u tlist = match tlist with
  | [] -> [u]
  | t :: q ->
      match compare_term u t with
      | 0 | -1 -> u :: tlist
      | _ -> t :: (sorted_add u q)

let rec sorted_merge tlist1 tlist2 = match tlist1, tlist2 with
  | [], _ -> tlist2
  | _, [] -> tlist1
  | t1::q1, t2::q2 -> 
      match compare_term t1 t2 with
      | 0 -> t1 :: t2 :: sorted_merge q1 q2
      | -1 -> t1 :: sorted_merge q1 tlist2
      | _ -> t2 :: sorted_merge tlist1 q2

let rec remove_first t tlist = match tlist with
  | [] -> []
  | t' :: q ->
      if equal t t'
      then remove_first t q
      else tlist 