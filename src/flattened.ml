open Term
open Utils

exception NoMatch

let ( let* ) o f = match o with
  | None -> None
  | Some x -> f x

let count_matching = ref 0

type compare_result =
  | Less
  | Eq
  | Unknown

module Flattened =
struct
  
  type term =
    | FVar of variable
    | FFunc of symbol * term list
    | FAC of symbol * (term * int) list

  type link += 
    | FTLink of term

  let dummy = FVar (fresh_variable ())

  type subst = (variable * term) list

  (*** Display ***)

  let rec string_of_term above_is_AC = function
    | FVar v -> string_of_variable v
    | FFunc(f,[]) -> f.f_name
    | FFunc(f,args) -> Printf.sprintf "%s(%s)" f.f_name (string_of_list (string_of_term false) "," args)
    | FAC(f,args) -> 
        if above_is_AC
        then Printf.sprintf "( %s )" (string_of_term_list_multiplicity f args)
        else string_of_term_list_multiplicity f args

  and string_of_term_list_multiplicity f = function
    | [] -> ""
    | [(t,1)] -> string_of_term true t
    | (t,1)::q -> string_of_term true t ^ " " ^ f.f_name ^ " " ^ string_of_term_list_multiplicity f q
    | (t,k)::q -> string_of_term true t ^ " " ^ f.f_name ^ " " ^ string_of_term_list_multiplicity f ((t,k-1)::q)

  let string_of_term t = string_of_term false t

  let string_of_subst subst = 
    if subst = []
    then "Id"
    else 
      "{ " ^
      string_of_list (fun (x,t) ->
        (string_of_variable x) ^ " -> " ^ (string_of_term t)
      ) "; " subst ^
      " }"

  let rec display_term = function 
    | FVar v -> print_string (string_of_variable v)
    | FFunc(f,[]) -> print_string f.f_name
    | FFunc(f,args) -> 
        Printf.printf "%s(" f.f_name;
        flush_all ();
        display_list (fun () -> ()) display_term "," args;
        print_string ")";
        flush_all ()

    | FAC(f,args) -> display_term_list_multiplicity f args

  and display_term_list_multiplicity f = function
  | [] -> ()
  | [(t,1)] -> display_term t;
  | (t,1)::q -> display_term t; print_string (" " ^ f.f_name ^ " "); display_term_list_multiplicity f q
  | (t,k)::q -> display_term t; print_string (" " ^ f.f_name ^ " "); display_term_list_multiplicity f ((t,k-1)::q)

  (*** Copy ***)

  let rec apply_renaming_preserving_compare = function 
    | FVar { v_link = VLink v'; _ } -> FVar v'
    | FVar v -> FVar v
    | FFunc(f,args) -> FFunc(f,List.map apply_renaming_preserving_compare args)
    | FAC(f,args) -> FAC(f,List.map (fun (t,k) -> apply_renaming_preserving_compare t, k) args)

  (*** Refresh ***)

  let rec refresh_no_cleanup = function
    | FVar { v_link = VLink v'; _ } -> FVar v'
    | FVar { v_link = FTLink t; _ } -> refresh_no_cleanup t
    | FVar v -> 
        let v' = fresh_variable () in
        link v (VLink v');
        FVar v'
    | FFunc(f,args) -> FFunc(f,List.map refresh_no_cleanup args)
    | FAC(f,args) -> FAC(f,List.map (fun (t,k) -> (refresh_no_cleanup t, k)) args)

  (*** Compare ***)

  let rec compare t1 t2 = match t1, t2 with
    | (FFunc(f1,_) | FAC(f1,_)), (FFunc(f2,_) | FAC(f2,_)) ->
        begin match compare_symbol f1 f2 with
        | 0 -> 
            begin match t1,t2 with
            | FFunc(_,args1), FFunc(_,args2) -> lexicographic_compare compare args1 args2
            | FAC(_,margs1), FAC(_,margs2) ->
                lexicographic_compare (fun (t1,k1) (t2,k2) -> match compare t1 t2 with
                | 0 -> if k1 < k2 then -1 else if k1 = k2 then 0 else 1
                | c -> c
              ) margs1 margs2
            | _ -> failwith "Unexpected"
            end
        | c -> c
        end
    | (FFunc _ | FAC _) , _ -> -1
    | _, (FFunc _ | FAC _) -> 1
    | FVar v1, FVar v2 -> compare_variable v1 v2

  let rec check_well_sorted = function 
    | FVar _ -> true
    | FFunc(_,args) -> List.for_all check_well_sorted args
    | FAC(f,margs) ->
        List.for_all (fun (t,k) -> match t with
          | FAC(g,_) when f == g -> false
          | _ -> true
        ) margs
        &&
        check_well_sorted_margs (List.hd margs) (List.tl margs)
      
  and check_well_sorted_margs (x,k) = function 
    | [] -> true
    | (x',k')::q -> 
        if compare x x' >= 0 then false else check_well_sorted_margs (x',k') q
    

  let rec merge tlist1 tlist2 = match tlist1, tlist2 with
    | [], _ -> tlist2
    | _, [] -> tlist1
    | (t1,k1)::q1, (t2,k2)::q2 -> 
        match compare t1 t2 with
        | 0 -> (t1,k1+k2) :: merge q1 q2
        | -1 -> (t1,k1) :: merge q1 tlist2
        | _ -> (t2,k2) :: merge tlist1 q2

  let rec merge_multiplicity tlist1 k1 tlist2 = match tlist1, tlist2 with
    | [], _ -> tlist2
    | _, [] -> List.map (fun (t1,k1') -> (t1,k1'*k1)) tlist1
    | (t1,k1')::q1, (t2,k2')::q2 -> 
        match compare t1 t2 with
        | 0 -> (t1,(k1*k1')+k2') :: merge_multiplicity q1 k1 q2
        | -1 -> (t1,(k1*k1')) :: merge_multiplicity q1 k1 tlist2
        | _ -> (t2,k2') :: merge_multiplicity tlist1 k1 q2

  let rec add_aux u k tlist = match tlist with
    | [] -> [(u,k)]
    | (t,k') :: q ->
        match compare u t with
        | 0 -> (t,k+k') :: q
        | -1 -> (u,k) :: tlist
        | _ -> (t,k') :: (add_aux u k q) 

  let add f u tlist = match u with 
    | FAC(g,args) when f == g -> merge args tlist 
    | _ -> add_aux u 1 tlist

  let add_multiplicity f u k tlist = match u with 
    | FAC(g,args) when f == g -> merge_multiplicity args k tlist 
    | _ -> add_aux u k tlist

  let rec of_term = function
    | Var v -> FVar v
    | Func(f,args) when f.f_cat = Syntactic -> FFunc(f,List.map of_term args)
    | Func(f,args) ->
        let args_flattened = List.map of_term args in
        let new_args = List.fold_left (fun acc u -> add f u acc) []  args_flattened in
        FAC(f,new_args)

  let rec to_term = function
    | FVar v -> Var v
    | FFunc(f,args) -> Func(f,List.map to_term args)
    | FAC(f,args) -> 
        to_term_list f args

  and to_term_list f args = match args with 
    | [] -> failwith "[Flattened.to_term_list] Unexpected case."
    | (t,k) :: q ->
        let t' = to_term t in
        to_term_list_aux f (to_term_unfold_arity f t' k) q

  and to_term_list_aux f acc = function 
    | [] -> acc
    | (t,k) :: tlist -> 
      let t' = to_term t in
      to_term_list_aux f (Func(f,[to_term_unfold_arity f t' k; acc])) tlist

  and to_term_unfold_arity f t k = to_term_unfold_arity_aux f t t k

  and to_term_unfold_arity_aux f t' acc = function
    | 1 -> acc
    | k -> to_term_unfold_arity_aux f t' (Func(f,[t';acc])) (k-1)

  let rec apply_symbol_aux f = function
    | [] -> []
    | t::q -> add f t (apply_symbol_aux f q)

  let apply_symbol f args = match f.f_cat with
    | Syntactic -> FFunc(f,args)
    | AC -> FAC(f,apply_symbol_aux f args)

  (*** Unfold Links ***)

  let rec unfold_AC_only f_AC acc_mterm (t,k) = match t with
    | FVar { v_link = FTLink t; _ } -> unfold_AC_only f_AC acc_mterm (t,k)
    | FAC(f,margs) when f == f_AC ->
        List.iter (fun (t',k') ->
          unfold_AC_only f_AC acc_mterm (t',k*k')
        ) margs
    | t -> acc_mterm := (t,k) :: !acc_mterm

  let rec unfold_rec_and_link_variables t = match t with
    | FVar v -> 
        begin match v.v_link with
          | NoLink -> link v Marked; t
          | Marked -> t
          | FTLink t' -> unfold_rec_and_link_variables t'
          | _ -> failwith "[Flattened.unfoled_rec_and_link_variables] Unexpected link." 
        end
    | FFunc(f,args) ->
        let args' = List.mapq unfold_rec_and_link_variables args in
        if args == args'
        then t
        else FFunc(f,args')
    | FAC(f,margs) ->
        let margs' = unfold_rec_and_link_variables_mterms f margs [] [] margs in
        if margs' == margs
        then t
        else FAC(f,margs')

  and unfold_rec_and_link_variables_mterms f orig_list rev_ordered unordered = function
    | [] -> 
        if unordered = []
        then orig_list
        else List.fold_left (fun acc (t,k) -> add_multiplicity f t k acc) (List.rev rev_ordered) unordered
    | (t,k) as mt :: q ->
        let t' = unfold_rec_and_link_variables t in
        if t == t'
        then unfold_rec_and_link_variables_mterms f orig_list (mt::rev_ordered) unordered q
        else unfold_rec_and_link_variables_mterms f orig_list rev_ordered ((t',k) :: unordered) q

  let unfold_rec_and_get_variables_term t = 
    auto_cleanup (fun () ->
      let t' = unfold_rec_and_link_variables t in
      let vars = !current_bound_vars in
      (vars,t')
    )

  let unfold_rec_and_get_variables_mterms f mt_l = 
    auto_cleanup (fun () ->
      let mt_l' = unfold_rec_and_link_variables_mterms f mt_l [] [] mt_l in
      let vars = !current_bound_vars in
      (vars,mt_l')
    )

  (*** Apply substitution ***)

  let rec copy_term_non_rec = function
    | FVar { v_link = FTLink t; _ } -> t
    | FVar _ as t -> t
    | FFunc(f,args) -> FFunc(f,List.map copy_term_non_rec args)
    | FAC(f,args) ->
        let copied_args = List.map (fun (x,k) -> copy_term_non_rec x, k) args in
        let new_args = List.fold_left (fun acc (u,k) -> add_multiplicity f u k acc) []  copied_args in
        FAC(f,new_args)

  let rec apply_subst subst t =
    auto_cleanup (fun () ->
      List.iter (fun (x,u) -> link x (FTLink u)) subst;
      copy_term_non_rec t
    )

  let rec copy_term_rec = function
    | FVar { v_link = FTLink t; _ } -> copy_term_rec t
    | FVar _ as t -> t
    | FFunc(f,args) -> FFunc(f,List.map copy_term_rec args)
    | FAC(f,args) ->
        let copied_args = List.map (fun (x,k) -> copy_term_rec x, k) args in
        let new_args = List.fold_left (fun acc (u,k) -> add_multiplicity f u k acc) []  copied_args in
        FAC(f,new_args)

  (*** Difference of variables ***)

  let diff_variables t1 t2 = 

    let rec go_through_t2 = function
    | FVar v when v.v_link = NoLink -> link v (VLink v)
    | FVar _ -> ()
    | FFunc(_,args) -> List.iter go_through_t2 args
    | FAC(_,args) -> List.iter (fun (t,_) -> go_through_t2 t) args
  in
  
  let rec go_through_t1 vars = function
    | FVar v when v.v_link = NoLink -> 
        vars := v :: !vars
    | FVar _ -> () 
    | FFunc(_,args) -> List.iter (go_through_t1 vars) args
    | FAC(_,args) -> List.iter (fun (t,_) -> go_through_t1 vars t) args
  in

  auto_cleanup (fun () ->
    go_through_t2 t2;
    let vars = ref [] in
    go_through_t1 vars t1;
    !vars
  )

  (*** Variable occurrence ***)

  let rec occurs x = function
    | FVar y -> x == y
    | FFunc(_,args) -> List.exists (occurs x) args
    | FAC(_,margs) -> List.exists (fun (t,_) -> occurs x t) margs 

  type link += OLink

  let rec get_variables = function 
    | FVar v -> 
        begin match v.v_link with 
        | NoLink -> link v OLink
        | OLink -> ()
        | _ -> failwith "[get_variables] Unexpected link"
        end
    | FFunc(_,args) -> List.iter get_variables args
    | FAC(_,margs) -> List.iter (fun (t,_) -> get_variables t) margs
    
  let get_variables_in_term t = 
    auto_cleanup (fun () ->
      get_variables t;
      !current_bound_vars
    )

  let get_variables_in_equations eq_list = 
    auto_cleanup (fun () ->
      List.iter (fun (t1,t2) ->
        get_variables t1;
        get_variables t2;
      ) eq_list;
      !current_bound_vars
    ) 

  (***************
    Equality 
  ****************)

  let rec equal t1 t2 = match t1, t2 with
    | FVar v1, FVar v2 -> v1 == v2
    | FFunc(f1,args1), FFunc(f2,args2) ->
        f1 == f2 && List.for_all2 equal args1 args2
    | FAC(f1,args1), FAC(f2,args2) ->
        f1 == f2 && 
        List.length args1 = List.length args2 && 
        List.for_all2 (fun (u1,k1) (u2,k2) -> k1 = k2 && equal u1 u2) args1 args2
    | _ -> false

  (***************
    AC - Compare 
  ****************)

  (*** EmbSmall [Definition 1] ***)

  let exists_embSmall pred f args = 

    let rec explore_args_v other_args = function
      | [] -> false
      | t::q  ->
          let new_args = add f t other_args in
          let new_term = FAC(f,new_args) in
          pred new_term || explore_args_v other_args q
    in

    let rec explore_AC_args_v other_args = function
      | [] -> false
      | (t,_)::q ->
          let new_args = add f t other_args in
          let new_term = FAC(f,new_args) in
          pred new_term || explore_AC_args_v other_args q
    in

    let rec explore prev_args = function 
      | [] -> false
      | (FFunc(h,args_v) as t,k) as tm ::q when less_symbol h f ->
          let init_res =
            if k = 1
            then explore_args_v (List.rev_append prev_args q) args_v
            else explore_args_v (List.rev_append prev_args ((t,k-1)::q)) args_v
          in
          init_res || explore (tm::prev_args) q
      | (FFunc _,k) as tm ::q -> explore (tm::prev_args) q
      | (FAC(h,args_v) as t,k) as tm ::q when less_symbol h f ->
          let init_res =
            if k = 1
            then explore_AC_args_v (List.rev_append prev_args q) args_v
            else explore_AC_args_v (List.rev_append prev_args ((t,k-1)::q)) args_v
          in
          init_res || explore (tm::prev_args) q
      | _ -> false
    in

    explore [] args

  let for_all_embSmall pred f args = 

    let rec explore_args_v other_args = function
      | [] -> true
      | t::q ->
          let new_args = add f t other_args in
          let new_term = FAC(f,new_args) in
          pred new_term && explore_args_v other_args q
    in

    let rec explore_AC_args_v other_args = function
      | [] -> true
      | (t,_)::q ->
          let new_args = add f t other_args in
          let new_term = FAC(f,new_args) in
          pred new_term && explore_AC_args_v other_args q
    in

    let rec explore prev_args = function 
      | [] -> true
      | (FFunc(h,args_v) as t,k) as tm ::q when less_symbol h f ->
          let init_res =
            if k = 1
            then explore_args_v (List.rev_append prev_args q) args_v
            else explore_args_v (List.rev_append prev_args ((t,k-1)::q)) args_v
          in
          init_res && explore (tm::prev_args) q
      | (FFunc _,k) as tm ::q -> explore (tm::prev_args) q
      | (FAC(h,args_v) as t,k) as tm ::q when less_symbol h f ->
          let init_res =
            if k = 1
            then explore_AC_args_v (List.rev_append prev_args q) args_v
            else explore_AC_args_v (List.rev_append prev_args ((t,k-1)::q)) args_v
          in
          init_res && explore (tm::prev_args) q
      | _ -> true
    in

    explore [] args

  (*** BigHead [Definition 1] and NoSmallHead ***)

  let check_Condition1_and_2 comp less_symb t args_t get_t s args_s get_s = 
    if 
      (* Case 1 *)
      List.exists (fun s_i -> comp t (get_s s_i) <> Unknown) args_s ||

      (* Case 2 *)
      (less_symb && List.for_all (fun t_i -> comp (get_t t_i) s = Less) args_t)
    then Less
    else Unknown

  let rec split f tlist = match tlist with
    | [] -> [],[],[]
    | (FVar _,_) :: _ -> [],[],tlist
    | ((FFunc(g,_) | FAC(g,_)),_) as tm :: q -> 
        let (small,big,vars) = split f q in
        if less_symbol f g 
        then (small,tm::big,vars)
        else (tm::small,big,vars)

  let rec diff tlist1 tlist2 = match tlist1, tlist2 with
    | [], _ -> ([],tlist2)
    | _, [] -> (tlist1,[])
    | (t1,k1)::q1, (t2,k2)::q2 ->
        match compare t1 t2 with
        | 0 -> 
            let (remain1,remain2) = diff q1 q2 in
            if k1 = k2
            then remain1, remain2
            else if k1 < k2
            then remain1, (t2,k2-k1)::remain2
            else (t1,k1-k2)::remain1, remain2
        | -1 -> 
            let (remain1,remain2) = diff q1 tlist2 in
            (t1,k1)::remain1, remain2
        | _ -> 
            let (remain1,remain2) = diff tlist1 q2 in
            remain1, (t2,k2)::remain2

  let rec check_Big_NoSmall_Head_Condition6 f list1 list2 = 
    
    (* Split list1 into smallHead1, bigHead1  and variables1
      and list2 into SmallHead2, bigHead2  and variables2 
      We follow up by computing the difference for all three list. *)

    let (small1,big1,vars1) = split f list1 
    and (small2,big2,vars2) = split f list2 in

    let (rbig1,rbig2) = diff big1 big2 in

    let unknown_big1 = 
      List.filter (fun (t1,_) ->
        List.for_all (fun (t2,_) -> compare_AC t1 t2 <> Less) rbig2
      ) rbig1
    in

    if unknown_big1 = []
    then 
      (* BigHead(t1) <= BigHead(t2) holds. We check NoSmallHead(t1) <= NoSmallHead(t2) *)
      let (rvars1,rvars2) = diff vars1 vars2 in
      let noSmallHead_result = 
        List.for_all (fun (t1,_) ->
          List.exists (fun (t2,_) -> compare_AC t1 t2 = Less) rbig2
        ) rvars1
      in
      if noSmallHead_result
      then 
        if (rbig1 <> [] || rbig2 <> [])
        then 
          (* BigHead(t1) < BigHead(t2) holds *)
          Less
        else
          (* If rvars1 <> [] then #(t1) <= #(t2) cannot holds*)
          if rvars1 = []
          then
            let (rsmall1,rsmall2) = diff small1 small2 in
            if rvars2 = [] && rsmall1 = [] && rsmall2 = []
            then Eq
            else
              let count_non_vars1 = List.fold_left (fun acc (_,k) -> acc + k) (List.fold_left (fun acc (_,k) -> acc + k) 0 rsmall1) big1 in
              let count_non_vars2 = List.fold_left (fun acc (_,k) -> acc + k) (List.fold_left (fun acc (_,k) -> acc + k) 0 rsmall2) big2 in
              if count_non_vars1 <= count_non_vars2 
              then 
                (* #(t1) <= #(t2) holds *)
                if count_non_vars1 < count_non_vars2 || rvars2 <> []
                then Less (* #(t1) < #(t2) holds *)
                else 
                  (* We need to check args1 < args2 *)
                  if 
                    List.for_all (fun (t1,_) ->
                      List.exists (fun (t2,_) -> compare_AC t1 t2 = Less) rsmall2 ||
                      List.exists (fun (t2,_) -> compare_AC t1 t2 = Less) rbig2
                    ) rsmall1
                  then Less
                  else Unknown
              else Unknown (* #(t1) <= #(t2) cannot holds *)
          else Unknown
      else Unknown
    else 
      (* If unknown_big1 <> [] then NoSmallHead(t1) <= NoSmallHead(t2) cannot hold *)
      Unknown

  and compare_AC_lex list1 list2 = match list1,list2 with
    | [], [] -> Eq
    | [], _ -> Less
    | _, [] -> Unknown
    | t1::q1, t2::q2 ->
        match compare_AC t1 t2 with
        | Eq -> compare_AC_lex q1 q2
        | c -> c
  
  and compare_AC t s = match t, s with
    | FVar x1 , FVar x2 -> if x1 == x2 then Eq else Unknown 
    | FVar x, FFunc(_,args) -> if List.exists (occurs x) args then Less else Unknown
    | FVar x, FAC(_,args) -> if List.exists (fun (u,_) -> occurs x u) args then Less else Unknown
    | FFunc(g,args_t), FFunc(f,args_s) when f == g ->
        begin match compare_AC_lex args_t args_s with
        | Eq -> Eq
        | c -> 
            if 
              (* Case 3 *)
              (c = Less && List.for_all (fun t_i -> compare_AC t_i s = Less) args_t) ||

              (* Case 1 *)
              List.exists (fun s_i -> compare_AC t s_i <> Unknown) args_s
            then Less
            else Unknown
        end
    | FAC(g,args_t), FAC(f,args_s) when f == g ->    
        begin match check_Big_NoSmall_Head_Condition6 f args_t args_s with
        | Eq -> Eq
        | c -> 
            if
              (* Case 6 *)
              (c = Less && for_all_embSmall (fun t' -> compare_AC t' s = Less) g args_t) ||

              (* Case 5 *)
              exists_embSmall (fun s' -> compare_AC t s' <> Unknown) f args_s ||

              (* Case 1 *)
              List.exists (fun (s_i,_) -> compare_AC t s_i <> Unknown) args_s
            then Less
            else Unknown
        end
    | FFunc(g,args_t), FFunc(f,args_s) -> 
        check_Condition1_and_2 compare_AC (less_symbol g f) t args_t (fun u -> u) s args_s (fun u -> u)
    | FFunc(g,args_t), FAC(f,args_s) -> 
        check_Condition1_and_2 compare_AC (less_symbol g f) t args_t (fun u -> u) s args_s (fun (u,_) -> u)
    | FAC(g,args_t), FFunc(f,args_s) -> 
        check_Condition1_and_2 compare_AC (less_symbol g f) t args_t (fun (u,_) -> u) s args_s (fun u -> u)
    | FAC(g,args_t), FAC(f,args_s) -> 
        check_Condition1_and_2 compare_AC (less_symbol g f) t args_t (fun (u,_) -> u) s args_s (fun (u,_) -> u)
    | _ -> Unknown  

  let compare_strong = compare_AC
  
  (* let compare_strong u v = 
    Statistic.record_notail Statistic.time_compare_strong (fun () -> compare_strong u v) *)

  (***************************************
    Elementary matching and unification
  ****************************************)

  module Elementary = struct

    let int2bin size =
      let buf = Bytes.create size in
      fun n ->
        for i = 0 to size - 1 do
          let pos = size - 1 - i in
          Bytes.set buf pos (if n land (1 lsl i) != 0 then '1' else '0')
        done;
        Bytes.to_string buf
    
    let display_matrix f_print m = 
      for i = 0 to Array.length m - 1 do 
        for j = 0 to Array.length m.(0) - 1 do
          Printf.printf "%s  " (f_print m.(i).(j))
        done;
        print_string "\n";
      done
    
    let display_vector f_print m = 
      for i = 0 to Array.length m - 1 do 
        Printf.printf "%s  " (f_print m.(i))
      done;
      print_string "\n"
      
    (* DFS Hullot Tree *)
    
    let dfs_hullot_tree f_next n all_bits constants_bits =
      let init_full_one = -1 lsr (Sys.int_size - n) in
    
      let big_enough subset_bits = List.for_all (fun vi -> subset_bits land vi <> 0) all_bits in
      let small_enough subset_bits = List.for_all (fun vi -> (subset_bits land vi) land ((subset_bits land vi) -1) = 0) constants_bits in
      
      (* When [sign_greater = true], it corresponds to >. *)
      let rec dfs next_dfs pre a k sign_greater = 
        let subset_bits, test = 
          if sign_greater 
          then pre lor a, big_enough (pre lor a)
          else pre, small_enough pre 
        in
        if test
        then 
          if k = 0
          then f_next next_dfs subset_bits
          else 
            let a' = a lsr 1 in
            dfs (fun () -> 
              dfs next_dfs (pre lor (a lxor a')) a' (k-1) false
            ) pre a' (k-1) true
        else next_dfs () 
      in
    
      dfs (fun () -> raise NoMatch) 0 init_full_one n true
    
    (** System of diophantine equation *)
    
    module Storage_solutions = struct
      type t = 
        {
          elts: (int Array.t list) Array.t;
          mutable nb_elts: int;
        }
    
      type t_frozen =
        {
          elts_f: (((int * bool) Array.t * int Array.t) list) Array.t;
          mutable nb_elts_f: int
        }
    
      type t_final = 
        {
          elts_t: (int Array.t Array.t) Array.t;
          associated_variables: term Array.t;   (** The fresh variables associated to the solutions that do not contain constants.
            We should have [Array.length associated_variables = Array.length elts.(nb_constants)]. They should also be all
            greater than the constant term in term of [Flattened.compare]. *)
          nb_elts_t: int;     (** Total number of solutions *)
          nb_constants: int;  (** Number of constants in the initial problem *)
          nb_variables: int   (** Number of variables in the initial problem *)
        }
    
      let display store =
        let count = ref 0 in
        Array.iteri (fun i elt ->
          if i = store.nb_constants
          then 
            begin 
              Printf.printf "- Variables :\n";
              Array.iteri (fun j sol ->
                Printf.printf "  Solution %d (local = %d) with associated vars = %s: " !count j (string_of_term store.associated_variables.(j));
                display_vector string_of_int sol;
                incr count
              ) elt
            end
          else
            begin 
              Printf.printf "- Constant %d:\n" i;
              Array.iteri (fun j sol ->
                Printf.printf "  Solution %d (local = %d): " !count j;
                display_vector string_of_int sol;
                incr count
              ) elt
            end
        ) store.elts_t
    
      let create nb_constant = { elts = Array.make (nb_constant+1) []; nb_elts = 0 } 
      let create_frozen nb_constant = { elts_f = Array.make (nb_constant+1) []; nb_elts_f = 0 } 
    
      let add storage idx sol = 
        storage.elts.(idx) <- sol::storage.elts.(idx);
        storage.nb_elts <- succ storage.nb_elts
    
      let add_frozen storage idx sol = 
        storage.elts_f.(idx) <- sol::storage.elts_f.(idx);
        storage.nb_elts_f <- succ storage.nb_elts_f
    
      let iter_frozen f storage_frozen = 
        Array.iteri (fun idx sol_list ->
          List.iter (f idx) sol_list
        ) storage_frozen.elts_f
      
      let for_all f storage = 
        Array.for_all (fun sols ->
          List.for_all f sols
        ) storage.elts
    
      (* Add the contant of store2 in store1 *)
      let merge store1 store2 = 
        store1.nb_elts <- store1.nb_elts + store2.nb_elts;
        Array.iteri (fun i sols2 ->
          store1.elts.(i) <- List.rev_append sols2 store1.elts.(i)
        ) store2.elts
    
      (* Convert a storage into a finalize storage *)
      let finalize nb_constants nb_variables storage = 
        let elts = Array.map (fun l -> Array.of_list l) storage.elts in
        let nb_assoc_variables = Array.length elts.(nb_constants) in
        let associated_variables = Array.make nb_assoc_variables dummy in
        for i = 0 to nb_assoc_variables - 1 do 
          associated_variables.(i) <- FVar (fresh_variable ())
        done;
        {
          elts_t = elts;
          associated_variables = associated_variables;
          nb_elts_t = storage.nb_elts;
          nb_constants = nb_constants;
          nb_variables = nb_variables
        }
    
      (** Generation of bitvectors of a variables/constants.
         When Solultions = { s_1, ..., s_p }, the bitvector of x of index i in solutions
         are b_1...b_p where b_j = 1 iff s_j(i) <> 0.
      *)
      let generate_bitvectors_of_variable storage idx = 
        let p = ref 0 in
        for i = 0 to Array.length storage.elts_t - 1 do
          for j = 0 to Array.length storage.elts_t.(i) -1 do 
            let p' = !p lsl 1 in
            p := if storage.elts_t.(i).(j).(idx) <> 0 then succ p' else p'
          done
        done;
        !p
    
      let generate_bitvectors_of_constant nb_remaing_solutions storage idx = 
        let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
        let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in
        (-1 lsr (Sys.int_size - nb_solution_of_constant_idx)) lsl nb_remaing_solutions
    
      let generate_bitvector_of_all_constants storage =
        let rec loop nb_remaing_solutions idx =
          if idx = storage.nb_constants
          then []
          else
            let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
            let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in
            ((-1 lsr (Sys.int_size - nb_solution_of_constant_idx)) lsl nb_remaing_solutions) :: loop nb_remaing_solutions (idx+1)
        in
        loop storage.nb_elts_t 0
    
      let generate_bitvectors storage = 
        let constant_bitvectors = generate_bitvector_of_all_constants storage in
        let all_bitvectors = ref constant_bitvectors in
        for idx = storage.nb_constants to storage.nb_constants + storage.nb_variables - 1 do
          all_bitvectors := generate_bitvectors_of_variable storage idx :: !all_bitvectors
        done;
        constant_bitvectors, !all_bitvectors
    
      (** Suitable_bitsubset_to_substitutions *)
      let suitable_bitsubset_to_substitution storage f_AC constants variables p = 
        
        let term_links = Array.make (Array.length variables) [] in
    
        let rec loop_vars i bit_i =
          (* Printf.printf "loop_vars(%d,%s)\n" i (int2bin storage.nb_elts_t bit_i); *)
          if i = -1
          then bit_i
          else
            if bit_i land p = 0 (* The subset do not contain the solution *)
            then loop_vars (i - 1) (bit_i lsl 1)
            else 
              begin 
                let sol = storage.elts_t.(storage.nb_constants).(i) in
                for j = 0 to Array.length term_links -1 do
                  let k = sol.(j+storage.nb_constants) in
                  if k <> 0
                  then term_links.(j) <- (storage.associated_variables.(i),k) :: term_links.(j)
                done;
                loop_vars (i - 1) (bit_i lsl 1)
              end
        in
    
        let rec loop_constants i constant sols_constant bit_i =
          (* Printf.printf "loop_constants(%d,%s,%s)\n" i (Flattened.string_of_term constant) (int2bin storage.nb_elts_t bit_i); *)
          if bit_i land p = 0 (* The subset do not contain the solution *)
          then loop_constants (i - 1) constant sols_constant (bit_i lsl 1)
          else 
            begin 
              let sol = sols_constant.(i) in
              for j = 0 to Array.length term_links -1 do
                let k = sol.(j+storage.nb_constants) in
                if k <> 0
                then term_links.(j) <- (constant,k) :: term_links.(j)
              done;
              (bit_i lsl (i + 1))
            end
        in
    
        let rec loop_all_constants ith_constant bit_i = 
          (* Printf.printf "loop_all_constants(%d,%s)\n" ith_constant (int2bin storage.nb_elts_t bit_i); *)
          if ith_constant = - 1
          then ()
          else
            let sols_constant = storage.elts_t.(ith_constant) in
            let bit_i' = loop_constants (Array.length sols_constant - 1) constants.(ith_constant) sols_constant bit_i in
            loop_all_constants (ith_constant-1) bit_i'
        in
    
        let bit_i = loop_vars (Array.length storage.associated_variables - 1) 1 in
        loop_all_constants (storage.nb_constants - 1) bit_i;
    
        for i = 0 to Array.length variables - 1 do
          match term_links.(i) with
            | [] -> failwith "[suitable_bitsubset_to_substitution] There should be a term to link."
            | [t,1] -> link variables.(i) (FTLink t)
            | mt -> link variables.(i) (FTLink (FAC(f_AC,mt)))
        done
    end
    
    (* In [solve_system_diophantine_equations nb_constants matrix_system], we assume that
       then first [nb_constants] columns of [matrix_system] represents constants. *)
    let solve_system_diophantine_equations nb_constants matrix_system =
      let nb_equations = Array.length matrix_system in
      let nb_variables = Array.length matrix_system.(0) in
    
      let defect (v:(int * bool) Array.t) = 
        let res = Array.make nb_equations 0 in
        for i = 0 to nb_equations - 1 do
          for j = 0 to nb_variables - 1 do
            res.(i) <- matrix_system.(i).(j) * (fst v.(j)) + res.(i)
          done
        done;
        res
      in
    
      let scalar_product v1 v2 = 
        let res = ref 0 in
        for i = 0 to nb_equations - 1 do
          res := !res + (v1.(i) * v2.(i))
        done;
        !res
      in
    
      let is_null v = Array.for_all (fun i -> i = 0) v in
    
      (* not (v + e_j >_m u) *)
      let order_vector j (v:(int * bool) Array.t) (u:int Array.t) =
    
        let rec loop all_geq i =
          if i = nb_variables 
          then all_geq
          else 
            let vi = if i = j then (fst v.(i)) + 1 else (fst v.(i)) in
            if vi < u.(i)
            then true
            else loop (all_geq && vi = u.(i)) (succ i)
        in
        loop true 0
      in
    
      (* v + e_j *)
      let add_ej (v:(int * bool) Array.t) j = 
        let v' = Array.copy v in
        let (vj,frozen) = v.(j) in
        v'.(j) <- (succ vj,frozen);
        v'
      in
    
      (* Generate the initial defects *)
      let initial_defects = Array.make nb_variables (Array.make 0 0) in
      
      for j = 0 to nb_variables - 1 do 
        let res = Array.make nb_equations 0 in
        for i = 0 to nb_equations - 1 do 
          res.(i) <- matrix_system.(i).(j)
        done;
        initial_defects.(j) <- res
      done;
    
      let set_rest_Mk = Storage_solutions.create nb_constants in
    
      (** The sets [set_Vk_not_in_Mk], [set_Vk_in_Mk] and [set_rest_Mk] are in fact arrays of size
          [nb_constants+1] that stores the solution depending on wether the solution corresponds to 
          a constant or not. *)
      let rec build_M (set_Vk_not_in_Mk:Storage_solutions.t_frozen) (set_Vk_in_Mk:Storage_solutions.t) =     
        if set_Vk_not_in_Mk.nb_elts_f = 0 && set_Vk_in_Mk.nb_elts = 0
        then ()
        else
          begin 
            let next_Vk_not_in_Mk = Storage_solutions.create_frozen nb_constants in
            let next_Vk_in_Mk = Storage_solutions.create nb_constants in
    
            Storage_solutions.iter_frozen (fun idx (v,defect_v) ->
              let success_j = ref [] in
              for j = 0 to nb_variables - 1 do
                if snd v.(j) || scalar_product defect_v initial_defects.(j) >= 0
                then ()
                else
                  if 
                    Storage_solutions.for_all (order_vector j v) set_Vk_in_Mk &&
                    Storage_solutions.for_all (order_vector j v) set_rest_Mk
                  then 
                    begin 
                      let new_v = add_ej v j in
                      let defect_new_v = defect new_v in
                      if is_null defect_new_v
                      then 
                        let new_v' = Array.map (fun (k,_) -> k) new_v in
                        Storage_solutions.add next_Vk_in_Mk idx new_v'
                      else 
                        begin 
                          List.iter (fun l ->
                            new_v.(l) <- (fst new_v.(l), true);
                          ) !success_j;
                          success_j := j :: !success_j;
                          Storage_solutions.add_frozen next_Vk_not_in_Mk idx (new_v,defect_new_v)
                        end
                    end
              done
            ) set_Vk_not_in_Mk;
    
            Storage_solutions.merge set_rest_Mk set_Vk_in_Mk;
    
            build_M next_Vk_not_in_Mk next_Vk_in_Mk
          end
      in
    
      let init_set_Vk_not_in_Mk = Storage_solutions.create_frozen nb_constants in
      let init_set_Vk_in_Mk = Storage_solutions.create nb_constants in
      
      for j = 0 to nb_variables - 1 do 
        if is_null initial_defects.(j)
        then 
          let ej = Array.make nb_variables 0 in
          ej.(j) <- 1;
          Storage_solutions.add init_set_Vk_in_Mk (min j nb_constants) ej
        else
          begin
            let ej = Array.make nb_variables (0,false) in
            for j' = 0 to max (nb_constants - 1) (j-1) do 
              ej.(j') <- (0,true)
            done;
            ej.(j) <- (1,j<nb_constants);
            Storage_solutions.add_frozen init_set_Vk_not_in_Mk (min j nb_constants) (ej,initial_defects.(j))
          end
      done;
    
      build_M init_set_Vk_not_in_Mk init_set_Vk_in_Mk;
    
      set_rest_Mk
    
    module MatrixGeneration = struct
    
      let dummy_vars = fresh_variable ()
    
      (* Should be improved when the terms will be DAG *)
      type t = 
        {
          mutable vars: (variable * int list) list;
          mutable nb_vars: int;
          mutable constants: (term * int list) list;
          mutable nb_constants: int;
          mutable nb_equations: int
        }
    
      let new_equations store = 
        store.vars <- List.map (fun (v,coeffs) -> (v,0 :: coeffs)) store.vars;
        store.constants <- List.map (fun (c,coeffs) -> (c,0 :: coeffs)) store.constants;
        store.nb_equations <- store.nb_equations + 1
    
      let rec fresh_coeff_column = function 
        | 0 -> []
        | n -> 0 :: fresh_coeff_column (n-1)
      
      let create_from_matching (vars_mt,const_mt) =
        let vars = 
          List.map (function 
            | FVar v, k -> v, [k]
            | _ -> failwith "[StorageTerm.create] Should only contain variables"
          ) vars_mt
        in
        let constants = 
          List.map (function 
            | t, k -> t, [(-k)]
          ) const_mt
        in
        {
          vars = vars;
          constants = constants;
          nb_vars = List.length vars_mt;
          nb_constants = List.length const_mt;
          nb_equations = 1
        }
    
      let create () = 
        {
          vars = [];
          nb_vars = 0;
          constants = [];
          nb_constants = 0;
          nb_equations = 0
        }
    
      let add_variable store v k = 
        let rec loop = function
          | [] -> (* The variable is greater than all *)
              let coeffs = fresh_coeff_column (store.nb_equations-1) in
              store.nb_vars <- store.nb_vars + 1;
              [v,k::coeffs]
          | ((v',coeffs) as v_coeff)::q_vars ->
              match compare_variable v v' with
              | 0 -> 
                  let coeffs' = match coeffs with
                    | coeff::q -> (k+coeff)::q
                    | [] -> failwith "[add_variable] A call to new_equations should be have made before."
                  in
                  (v',coeffs') :: q_vars
              | -1 -> 
                  (* The variable was not recorded *)
                  let coeffs = fresh_coeff_column (store.nb_equations-1) in
                  store.nb_vars <- store.nb_vars + 1;
                  (v,k::coeffs) :: v_coeff :: q_vars
              | _ -> v_coeff :: loop q_vars
        in
        store.vars <- loop store.vars
    
      let add_constant store t k = 
        let rec loop = function
          | [] -> (* The constant is greater than all *)
              let coeffs = fresh_coeff_column (store.nb_equations-1) in
              store.nb_constants <- store.nb_constants + 1;
              [t,k::coeffs]
          | ((t',coeffs) as t_coeff)::q_const ->
              match compare t t' with
              | 0 -> 
                  let coeffs' = match coeffs with
                    | coeff::q -> (k+coeff)::q
                    | [] -> failwith "[add_constant] A call to new_equations should be have made before."
                  in
                  (t',coeffs') :: q_const
              | -1 -> 
                  (* The variable was not recorded *)
                  let coeffs = fresh_coeff_column (store.nb_equations-1) in
                  store.nb_constants <- store.nb_constants + 1;
                  (t,k::coeffs) :: t_coeff :: q_const
              | _ -> t_coeff :: loop q_const
        in
        store.constants <- loop store.constants
    
      let convert_store store = 
        let matrix = Array.make_matrix store.nb_equations (store.nb_constants + store.nb_vars) 0 in
        let variables = Array.make store.nb_vars dummy_vars in
        let constants = Array.make store.nb_constants dummy in
    
        List.iteri (fun j (t,coeffs) ->
          constants.(j) <- t;
          List.iteri (fun i k ->
            matrix.(i).(j) <- k
          ) coeffs  
        ) store.constants;
    
        List.iteri (fun j (v,coeffs) ->
          variables.(j) <- v;
          List.iteri (fun i k ->
            matrix.(i).(store.nb_constants+j) <- k
          ) coeffs  
        ) store.vars;
    
        (matrix,variables,store.nb_vars,constants,store.nb_constants)
    
      let from_matching_equations system_equations = 
        (* Printf.printf "System of equations:\n";
        List.iter (fun (left,right) ->
          print_string "left: ";
          List.iter (fun (t,k) -> Printf.printf "(%s,%d) " (string_of_term t) k) left;
          print_string ", right: ";
          List.iter (fun (t,k) -> Printf.printf "(%s,%d) " (string_of_term t) k) right;
          print_string "\n";
        ) system_equations; *)
        match system_equations with
        | [] -> failwith "[Flattened.Elementary.MatrixGeneration.from_matching_equations] The system of equations should not be empty"
        | (vars_list,const_list)::q ->
            if vars_list = [] || const_list = [] then failwith "[Flattened.Elementary.MatrixGeneration.from_matching_equations] An equation should not have an empty left or right hand side.";
            
            let store = create_from_matching (vars_list,const_list) in

            List.iter (fun (vars_l,const_l) ->
              if vars_l = [] || const_l = [] then failwith "[Flattened.Elementary.MatrixGeneration.from_matching_equations] An equation should not have an empty left or right hand side.";
              new_equations store;
              List.iter (function (t,k) -> match t with 
                | FVar v -> add_variable store v k
                | _ -> failwith "[from_matching_equations] Should be a variable"
              ) vars_l;
              List.iter (function (t,k) -> add_constant store t (-k)) const_l
            ) q;
    
            convert_store store
    
      let from_unification_equations system_equations = 
        let store = create () in
        List.iter (fun (left_eq,right_eq) ->
          new_equations store;
          List.iter (function (t,k) -> match t with 
            | FVar v -> add_variable store v k 
            | _ -> add_constant store t k
          ) left_eq;
          List.iter (function (t,k) -> match t with 
            | FVar v -> add_variable store v (-k) 
            | _ -> add_constant store t (-k)
          ) right_eq;
        ) system_equations;
    
        convert_store store
    end 
    
    let solve f_next f_AC matrix_system variables nb_variables constants nb_constants =
      (* print_string "Matrix =\n";
      display_matrix string_of_int matrix_system;
      Printf.printf "Variables (%d)=\n" nb_variables;
      display_vector string_of_variable variables;
      Printf.printf "Constants (%d)=\n" nb_constants;
      display_vector string_of_term constants; *)
      
      (* Solving the matrix system *)
      let solutions = solve_system_diophantine_equations nb_constants matrix_system in
      let nb_solutions = solutions.Storage_solutions.nb_elts in
      
      if nb_solutions > Sys.int_size - 2
      then failwith "Limit on the number of solutions reached";
    
      if nb_solutions = 0 then raise NoMatch;
    
      let finalized_solutions = Storage_solutions.finalize nb_constants nb_variables solutions in
    
      (* Printf.printf "\n** Finalized solution\n";
      Storage_solutions.display finalized_solutions; *)
    
      (* Bit presentation to subset of solutions *)
      let (constant_bitvectors,all_bitvectors) = Storage_solutions.generate_bitvectors finalized_solutions in
    
      (* Printf.printf "\n** Constant bitvectors\n";
      List.iter (fun p ->
        Printf.printf "bit = %s\n" (int2bin nb_solutions p)
      ) constant_bitvectors;
      Printf.printf "\n** All bitvectors\n";
      List.iter (fun p ->
        Printf.printf "bit = %s\n" (int2bin nb_solutions p)
      ) all_bitvectors; *)
    
      dfs_hullot_tree (fun f_next_dfs p ->
        try 
          auto_cleanup_noreset (fun () ->
            (* Printf.printf "Building the substitution with %s\n" (int2bin nb_solutions p); *)
            Storage_solutions.suitable_bitsubset_to_substitution finalized_solutions f_AC constants variables p;
            f_next ()
          )
        with NoMatch -> f_next_dfs ()
      ) nb_solutions all_bitvectors constant_bitvectors
    
    (** [system_equations] is a list of pairs of multiplicty list. The left hand side are only
        variables and on the right hand side, they are considered as constant. *)
    let matching f_next f_AC system_equations = 
      if system_equations = [] then failwith "[Elementary.matching] The system of equations should not be empty.";
      let (matrix_system,variables,nb_variables,constants,nb_constants) = MatrixGeneration.from_matching_equations system_equations in
    
      solve f_next f_AC matrix_system variables nb_variables constants nb_constants
    
    let unification f_next f_AC system_equations = 
      let (matrix_system,variables,nb_variables,constants,nb_constants) = MatrixGeneration.from_unification_equations system_equations in
    
      solve f_next f_AC matrix_system variables nb_variables constants nb_constants
      
  end

  (***************
    Matching 
  ****************)

  let maude_string_of_variable v =
    Maude_function.record_old_variable v;
    "X" ^ (string_of_int v.v_id) ^ ":Bitstring" 

  let rec maude_string_of_term_list str_t = function
    | 1 -> str_t
    | k -> str_t ^ "," ^ maude_string_of_term_list str_t (k-1)

  let rec maude_string_of_term_multiplicity f (t,k) =
    let str_t = maude_string_of_term t in
    if k = 1 
    then str_t
    else f.f_name ^ "(" ^ (maude_string_of_term_list str_t k) ^ ")"
  
  and maude_string_of_term = function
    | FVar v -> maude_string_of_variable v
    | FFunc(f,[]) -> f.f_name
    | FFunc(f,args) -> f.f_name ^ "(" ^ (string_of_list maude_string_of_term "," args) ^ ")"
    | FAC(f,[tm]) -> maude_string_of_term_multiplicity f tm
    | FAC(f,args) -> 
        f.f_name ^ "(" ^ (string_of_list (maude_string_of_term_multiplicity f)  "," args) ^ ")"

  let maude_get_matching maude_out =
    let lexbuf = (Lexing.from_channel maude_out) in
    Maude_parser.matching Maude_lexer.token lexbuf
  
  let maude_make_matching_query limit eq_list maude_in =
    let left_str, right_str =
      List.fold_left (fun (l_str,r_str) (s,t) ->
        ((maude_string_of_term s) ^ " " ^ l_str),((maude_string_of_term t) ^ " " ^ r_str)
      ) ("","") eq_list
    in 
    let str_limit = match limit with
      | None -> ""
      | Some n -> " [" ^ (string_of_int n) ^ "]"
    in
    (* Printf.printf "match%s %s <=? %s .\n" str_limit left_str right_str;
    flush_all (); *)
    Printf.fprintf maude_in "match%s %s <=? %s .\n" str_limit left_str right_str
  
  let number_of_call = ref 0

  let maude_matching limit eq_list =
    incr number_of_call;
    let result = 
      Maude_function.run_maude (maude_make_matching_query limit eq_list) (fun chan -> maude_get_matching chan)
    in
    Hashtbl.clear Maude_function.old_variable_table;
    Hashtbl.clear Maude_function.fresh_variable_table;
    List.map (fun subst -> List.map (fun (x,t) -> (x,of_term t)) subst) result

  let maude_matching limit eq_list = 
    Statistic.record_notail Statistic.time_maude_matching (fun () -> maude_matching limit eq_list)
  
  module Basic = struct

    let var_context = { v_name = "_"; v_id = 0; v_link = NoLink  }
    let term_var_context = FVar var_context

    let display_remaining_problems rem = 
      List.iter (fun (f,exact,left,right) ->
        Printf.printf "Symbol:%s, exact:%b, left:" f.f_name exact;
        List.iter (fun (t,k) -> Printf.printf "(%s,%d) " (string_of_term t) k) left;
        print_string ", right: ";
        List.iter (fun (t,k) -> Printf.printf "(%s,%d) " (string_of_term t) k) right;
        print_string "\n"
      ) rem

    let rec matching_multiplicity_bound_vars f rest_unbound_vars1 vars1 list2 = 
      if !rule_computed = 7644 then 
        begin
          Printf.printf "matching_multiplicity_bound_vars: f=%s, rest_unbound_vars1=" f.f_name;
          display_list (fun () -> print_string "[]") (fun (t,k) -> Printf.printf "(%s,%d)" (string_of_term t) k) "; " rest_unbound_vars1;
          print_string ", vars1=";
          display_list (fun () -> print_string "[]") (fun (t,k) -> Printf.printf "(%s,%d)" (string_of_term t) k) "; " vars1;
          print_string ", list2=";
          display_list (fun () -> print_string "[]") (fun (t,k) -> Printf.printf "(%s,%d)" (string_of_term t) k) "; " list2; 
          print_string "\n";
          flush_all ()
        end;
      match vars1 with
      | [] -> List.rev rest_unbound_vars1, list2
      | (FVar { v_link = FTLink (FAC(g,args1)); _ } ,k1) ::q1 when f == g ->
          matching_multiplicity_bound_vars f rest_unbound_vars1 q1 (matching_multicity_bound_vars_one_list args1 k1 list2)
      | (FVar { v_link = FTLink t1'; _ } ,k1) ::q1 ->
          matching_multiplicity_bound_vars f rest_unbound_vars1 q1 (matching_multicity_bound_vars_one t1' k1 [] list2)
      | mt1 :: q1 -> matching_multiplicity_bound_vars f (mt1::rest_unbound_vars1) q1 list2
    
    and matching_multicity_bound_vars_one_list list1 k1' list2 = match list1 with 
      | [] -> list2
      | (t1,k1)::q1 -> 
          matching_multicity_bound_vars_one_list q1 k1' (matching_multicity_bound_vars_one t1 (k1*k1') [] list2)

    and matching_multicity_bound_vars_one t1' k1 rest2 list2 = match list2 with
      | [] -> raise NoMatch
      | (t2,k2) as mt2 ::q2 -> 
          match compare t1' t2 with 
          | -1 -> raise NoMatch
          | 1 ->  matching_multicity_bound_vars_one t1' k1 (mt2::rest2) q2
          | _ ->
              if k1 = k2 
              then List.rev_append rest2 q2
              else 
                if k2 < k1 
                then raise NoMatch 
                else List.rev_append rest2 ((t2,k2-k1)::q2)

    (** The variable [remaining_problems] should only contain variables on the left side *)
    let rec matching f_next remaining_problems t1 t2 = match t1, t2 with
      | FVar { v_link = FTLink t1'; _ }, _ -> 
          if equal t1' t2 
          then f_next remaining_problems
          else raise NoMatch
      | FVar v, _ -> 
        auto_cleanup_noreset (fun () -> link v (FTLink t2); f_next remaining_problems)
      | _, FVar _ -> raise NoMatch
      | FFunc(f1,args1), FFunc(f2,args2) -> 
          if f1 != f2 then raise NoMatch;
          matching_list f_next remaining_problems args1 args2
      | FAC(f1,args1), FAC(f2,args2) ->
          if f1 != f2 then raise NoMatch;
          let count_term1 = List.fold_left (fun acc (_,k) -> k + acc) 0 args1 in
          let count_term2 = List.fold_left (fun acc (_,k) -> k + acc) 0 args2 in
          if count_term1 > count_term2 then raise NoMatch;
          matching_multiplicity f_next remaining_problems true f1 args1 args2
      | _ -> raise NoMatch

    and matching_list f_next remaining_problems list1 list2 = match list1,list2 with
      | [], [] -> f_next remaining_problems
      | t1::q1, t2::q2 ->
          matching (fun remaining_problems1 ->
            matching_list f_next remaining_problems1 q1 q2 
          ) remaining_problems t1 t2
      | [],_ | _,[] -> failwith "[matching_list] Unexpected case"

    and matching_multiplicity f_next remaining_problems exact f list1 list2 = 
      if !rule_computed = 7644 then 
        begin
          Printf.printf "** matching_multiplicity: f=%s, list1=" f.f_name;
          display_list (fun () -> print_string "[]") (fun (t,k) -> Printf.printf "(%s,%d)" (string_of_term t) k) "; " list1;
          print_string ", list2=";
          display_list (fun () -> print_string "[]") (fun (t,k) -> Printf.printf "(%s,%d)" (string_of_term t) k) "; " list2; 
          print_string "\n";
          Printf.printf "Remaing problems:\n";
          display_remaining_problems remaining_problems;
          let subst = 
            List.map (fun v -> match v.v_link with 
              | FTLink t -> (v,t)
              | _ -> failwith "[exists_matching_multiplicity] Unexpected case"
            ) !current_bound_vars
          in
          Printf.printf "Current substitution: %s\n" (string_of_subst subst);
          flush_all ()
        end;
      match list1 with 
      | [] -> 
          if exact 
          then 
            if list2 <> []
            then raise NoMatch
            else f_next remaining_problems
          else
            begin match list2 with
            | [] -> f_next remaining_problems
            | [t,1] -> 
                auto_cleanup_noreset (fun () ->
                  link var_context (FTLink t);
                  f_next remaining_problems
                )
            | _ -> 
                auto_cleanup_noreset (fun () ->
                  link var_context (FTLink (FAC(f,list2)));
                  f_next remaining_problems
                )
            end
      | (FVar _,_)::_ -> 
          let unbound_rest1, rest2 = matching_multiplicity_bound_vars f [] list1 list2 in
          begin match unbound_rest1 = [], rest2 = [] with
          | true, true -> f_next remaining_problems
          | false, true -> raise NoMatch
          | true, false ->
              if exact
              then raise NoMatch
              else
                begin match rest2 with
                | [] -> f_next remaining_problems
                | [t,1] -> 
                    auto_cleanup_noreset (fun () ->
                      link var_context (FTLink t);
                      f_next remaining_problems
                    )
                | _ -> 
                    auto_cleanup_noreset (fun () ->
                      link var_context (FTLink (FAC(f,rest2)));
                      f_next remaining_problems
                    )
                end
          | false,false -> f_next ((f,exact,unbound_rest1, rest2)::remaining_problems)
          end
      | ((FFunc(f1,_) | FAC(f1,_)) as t1,k1)::q1 ->
          matching_multiplicity_one (fun remaining_problems1 rest2 ->
            matching_multiplicity f_next remaining_problems1 exact f q1 rest2
          ) remaining_problems f1 t1 k1 [] list2
        
    and matching_multiplicity_one f_next remaining_problems f1 t1 k1 rest2 list2 = 
      if !rule_computed = 7644 then 
        begin
          Printf.printf "matching_multiplicity_one: f1=%s, t1=%s, k1=%d, rest2=" f1.f_name (string_of_term t1) k1;
          display_list (fun () -> print_string "[]") (fun (t,k) -> Printf.printf "(%s,%d)" (string_of_term t) k) "; " rest2;
          print_string ", list2=";
          display_list (fun () -> print_string "[]") (fun (t,k) -> Printf.printf "(%s,%d)" (string_of_term t) k) "; " list2; 
          print_string "\n";
          Printf.printf "Remaing problems:\n";
          display_remaining_problems remaining_problems;
          let subst = 
            List.map (fun v -> match v.v_link with 
              | FTLink t -> (v,t)
              | _ -> failwith "[exists_matching_multiplicity] Unexpected case"
            ) !current_bound_vars
          in
          Printf.printf "Current substitution: %s\n" (string_of_subst subst);
          flush_all ()
        end;
      match list2 with
      | [] -> raise NoMatch
      | ((FFunc(f2,_) | FAC(f2,_)) as t2,k2) as mt2 ::q2 ->
          begin match compare_symbol f1 f2 with 
          | -1 -> raise NoMatch
          | 1 ->  matching_multiplicity_one f_next remaining_problems f1 t1 k1 (mt2::rest2) q2
          | _ ->
              try 
                matching (fun remaining_problems1 ->
                  if k1 = k2
                  then f_next remaining_problems1 (List.rev_append rest2 q2)
                  else f_next remaining_problems1 (List.rev_append rest2 ((t2,k2-k1)::q2))
                ) remaining_problems t1 t2 
              with NoMatch -> 
                matching_multiplicity_one f_next remaining_problems f1 t1 k1 (mt2::rest2) q2
          end
      | _ -> raise NoMatch

    let rec partition_remaining_problems_simple f_target = function
      | [] -> [], []
      | (f,_,vars1,list2) :: q when f == f_target ->
          let same_f_problems, other_problems = partition_remaining_problems_simple f_target q in
          (vars1,list2)::same_f_problems, other_problems
      | pbl::q -> 
          let same_f_problems, other_problems = partition_remaining_problems_simple f_target q in
          same_f_problems, pbl::other_problems

    let rec partition_remaining_problems f_target = function
      | [] -> None, [], []
      | (f,exact,vars1,list2) :: q when f == f_target ->
          if not exact 
          then 
            begin 
              (* if !rule_computed = 7644 then 
                begin
                  Printf.printf "partition_remaining_problems - matching_multiplicity_bound_vars\n";
                  let subst = 
                    List.map (fun v -> match v.v_link with 
                      | FTLink t -> (v,t)
                      | _ -> failwith "[exists_matching_multiplicity] Unexpected case"
                    ) !current_bound_vars
                  in
                  Printf.printf "Current substitution: %s\n" (string_of_subst subst);
                end; *)
              let vars1',list2' = matching_multiplicity_bound_vars f [] vars1 list2 in
              match vars1' = [], list2' = [] with
              | true, true -> 
                  let same_f_problems, other_problems = partition_remaining_problems_simple f_target q in
                  None, same_f_problems, other_problems
              | false, true -> raise NoMatch
              | _ -> 
                  let same_f_problems, other_problems = partition_remaining_problems_simple f_target q in
                  Some (vars1',list2'), same_f_problems, other_problems
            end
          else
            begin 
              (* if !rule_computed = 7644 then 
                begin
                  Printf.printf "partition_remaining_problems 2 - matching_multiplicity_bound_vars\n";
                  let subst = 
                    List.map (fun v -> match v.v_link with 
                      | FTLink t -> (v,t)
                      | _ -> failwith "[exists_matching_multiplicity] Unexpected case"
                    ) !current_bound_vars
                  in
                  Printf.printf "Current substitution: %s\n" (string_of_subst subst);
                end; *)
              let vars1',list2' = matching_multiplicity_bound_vars f [] vars1 list2 in
              match vars1' = [], list2' = [] with
              | true, true -> partition_remaining_problems f_target q
              | true, false 
              | false, true -> raise NoMatch
              | _ ->
                  let not_exact_pbl, same_f_problems, other_problems = partition_remaining_problems f_target q in
                  not_exact_pbl, ((vars1',list2')::same_f_problems), other_problems
            end
      | pbl::q -> 
          let not_exact_pbl, same_f_problems, other_problems = partition_remaining_problems f_target q in
          not_exact_pbl, same_f_problems, pbl::other_problems

    let rec matching_variables f_next remaining_problems = match remaining_problems with
      | [] -> f_next ()
      | (f,_,_,_) :: _ ->
          let not_exact_pbl, same_f_problems, other_problems = partition_remaining_problems f remaining_problems in
          match not_exact_pbl with
          | None ->
              if same_f_problems = []
              then matching_variables f_next other_problems
              else
                Elementary.matching (fun () ->
                  matching_variables f_next other_problems
                ) f same_f_problems
          | Some (vars1,list2) ->
              try 
                (* We first try strict matching *)
                if vars1 = [] then raise NoMatch;
                Elementary.matching (fun () ->
                  matching_variables f_next other_problems
                ) f ((vars1,list2)::same_f_problems)
              with NoMatch ->
                if vars1 = []
                then 
                  match list2 with 
                  | [(t,1)] -> 
                      auto_cleanup_noreset (fun () -> 
                        link var_context (FTLink t);
                        matching_variables f_next other_problems
                      )
                  | _ -> 
                      auto_cleanup_noreset (fun () -> 
                        link var_context (FTLink (FAC(f,list2)));
                        matching_variables f_next other_problems
                      )
                else
                  Elementary.matching (fun () ->
                    matching_variables f_next other_problems
                  ) f (((term_var_context,1)::vars1,list2)::same_f_problems)

    let matching_all t1 t2 = 
      let all_subst = ref [] in
      try 
        auto_cleanup (fun () ->
          matching (fun remaining_problems ->
            matching_variables (fun () ->
              let subst = 
                List.map (fun v -> match v.v_link with 
                  | FTLink t -> (v,t)
                  | _ -> failwith "[matching_one] Unexpected case"
                ) !current_bound_vars
              in
              all_subst := subst :: !all_subst;
              raise NoMatch
            ) remaining_problems
          ) [] t1 t2
        )
      with NoMatch -> !all_subst

    let find_matching_term_list list1 list2 = 
      try 
        auto_cleanup (fun () ->
          matching_list (fun remaining_problems ->
            matching_variables (fun () ->
              let subst = 
                List.map (fun v -> match v.v_link with 
                  | FTLink t -> (v,t)
                  | _ -> failwith "[exists_matching] Unexpected case"
                ) !current_bound_vars
              in
              Some subst
            ) remaining_problems
          ) [] list1 list2
        )
      with NoMatch -> None

    let subst_implies vars subst1 subst2 =
      let list1 = List.map (fun v -> apply_subst subst1 (FVar v)) vars in
      let list2 = List.map (fun v -> apply_subst subst2 (FVar v)) vars in
  
      find_matching_term_list list1 list2
  
    let is_subst_implies vars subst1 subst2 =
      let list1 = List.map (fun v -> apply_subst subst1 (FVar v)) vars in
      let list2 = List.map (fun v -> apply_subst subst2 (FVar v)) vars in
  
      None <> find_matching_term_list list1 list2
  
    let verify_minimality t1 t2 subst_list =
      let header_printed = ref false in
      let vars = get_variables_in_term t1 in
  
      let rec loop visited_subst = function 
        | [] -> visited_subst
        | subst :: q_subst ->
            if List.exists (fun subst' -> is_subst_implies vars subst' subst) visited_subst
            then loop visited_subst q_subst
            else loop (subst :: (List.filter_rev (fun subst' -> not (is_subst_implies vars subst subst')) visited_subst)) q_subst
      in
  
      let minimal_set_size = List.length (loop [] subst_list) in
      let set_size = List.length subst_list in
  
      if minimal_set_size <> set_size
      then 
        begin 
          header_printed := true;
          Printf.printf "*** Matching %d not minimal in %s -> %s\n" !count_matching (string_of_term t1) (string_of_term t2);
          Printf.printf "  Number of substitutions in original set: %d\n" set_size;
          Printf.printf "  Number of substitutions in minimal set: %d\n" minimal_set_size;
          Printf.printf "  Gain: %d\n" (set_size - minimal_set_size)
        end

    let matching_one t1 t2 = 
      (* Maude_function.record_maude_query (maude_make_matching_query None [t1,t2]);  *)
      (* verify_minimality t1 t2 (matching_all t1 t2); *)
      try 
        auto_cleanup (fun () ->
          matching (fun remaining_problems ->
            matching_variables (fun () ->
              let subst = 
                List.map (fun v -> match v.v_link with 
                  | FTLink t -> (v,t)
                  | _ -> failwith "[matching_one] Unexpected case"
                ) !current_bound_vars
              in
              Some subst
            ) remaining_problems
          ) [] t1 t2
        )
      with NoMatch -> None

    let exists_matching pred t1 t2 = 
      (* Maude_function.record_maude_query (maude_make_matching_query None [t1,t2]); *)
      (* verify_minimality t1 t2 (matching_all t1 t2); *)
      try 
        auto_cleanup (fun () ->
          matching (fun remaining_problems ->
            matching_variables (fun () ->
              let subst = 
                List.map (fun v -> match v.v_link with 
                  | FTLink t -> v.v_link <- NoLink; (v,t)
                  | _ -> failwith "[exists_matching] Unexpected case"
                ) !current_bound_vars
              in
              if auto_cleanup (fun () -> pred subst)
              then 
                begin 
                  (* Restore link *)
                  List.iter (fun (v,t) -> v.v_link <- FTLink t) subst;
                  true
                end 
              else 
                begin 
                  (* Restore link *)
                  List.iter (fun (v,t) -> v.v_link <- FTLink t) subst;
                  raise NoMatch
                end 
            ) remaining_problems
          ) [] t1 t2
        )
      with NoMatch -> false

    (* Matching with context : C[u\sigma] =_AC v *)
    let exists_matching_with_context pred t1 t2 =  
      let rec go_through_position context sub_t2 = match sub_t2 with
        | FVar _ -> exists_matching (fun subst -> pred context subst) t1 sub_t2
        | FFunc(f,args) ->
            exists_matching (fun subst -> pred context subst) t1 sub_t2 ||
            go_through_position_list (fun args' -> context (FFunc(f,args'))) args
        | FAC(f,args2) ->
            match t1 with
            | FAC(g,args1) when f == g -> 
                (* We will test the inclusion *)
                begin try 
                  auto_cleanup (fun () ->
                    matching_multiplicity (fun remaining_problems ->
                      matching_variables (fun () -> 
                        let (subst',context') = match var_context.v_link with
                          | NoLink ->
                              (* The matching was strict *)
                              let subst = 
                                List.map (fun v -> match v.v_link with 
                                  | FTLink t -> v.v_link <- NoLink; (v,t)
                                  | _ -> failwith "[exists_matching_multiplicity] Unexpected case"
                                ) !current_bound_vars
                              in
                              subst,context
                          | FTLink t ->
                              (* The matching was not strict *)
                              let subst = 
                                List.map (fun v -> match v.v_link with 
                                  | FTLink t -> v.v_link <- NoLink; (v,t)
                                  | _ -> failwith "[exists_matching_multiplicity] Unexpected case"
                                ) !current_bound_vars
                              in
                              begin match t with
                              | FAC(g,args) when f == g -> 
                                  let context' t' = context (FAC(f,add f t' args)) in
                                  subst,context'
                              | _ ->
                                  let context' t' = context (FAC(f,add f t' [t,1])) in
                                  subst,context'
                              end
                          | _ -> failwith "Wrong link"
                        in
                        if auto_cleanup (fun () -> pred context' subst')
                        then 
                          begin 
                            (* Restore link *)
                            List.iter (fun (v,t) -> v.v_link <- FTLink t) subst';
                            true 
                          end
                        else 
                          begin 
                            (* Restore link *)
                            List.iter (fun (v,t) -> v.v_link <- FTLink t) subst';
                            raise NoMatch
                          end 
                      ) remaining_problems
                    ) [] false f args1 args2
                  )
                with NoMatch -> 
                  go_through_position_list_multiplicity f (fun args' -> context (FAC(f,args'))) args2
                end
            | _ ->
                exists_matching (fun subst -> pred context subst) t1 sub_t2 ||
                go_through_position_list_multiplicity f (fun args' -> context (FAC(f,args'))) args2

      and go_through_position_list context = function
        | [] -> false
        | t::q -> 
            go_through_position (fun t' -> context (t'::q)) t ||
            go_through_position_list (fun args' -> context (t :: args')) q
  
      and go_through_position_list_multiplicity f context = function
        | [] -> false
        | (t,1)::q ->
            go_through_position (fun t' -> context (add f t' q)) t ||
            go_through_position_list_multiplicity f (fun args' -> context (add f t args')) q
        | (t,k)::q ->
            go_through_position (fun t' -> context (add f t' ((t,k-1)::q))) t ||
            go_through_position_list_multiplicity f (fun args' -> context (add_multiplicity f t k args')) q
      in
  
      go_through_position (fun t -> t) t2 

    let matching_with_context_one t1 t2 =
      if !rule_computed = 7644 then 
        begin
          Printf.printf "matching_with_context_one: %s with %s\n" (string_of_term t1) (string_of_term t2);
          flush_all ()
        end;
      let rec go_through_position context sub_t2 = match sub_t2 with
        | FVar _ -> 
            begin match matching_one t1 sub_t2 with 
            | None -> None
            | Some subst -> Some (context,subst)
            end
        | FFunc(f,args) ->
            begin match matching_one t1 sub_t2 with
            | Some subst -> Some (context,subst)
            | None -> go_through_position_list (fun args' -> context (FFunc(f,args'))) args
            end
        | FAC(f,args2) ->
            match t1 with
            | FAC(g,args1) when f == g -> 
                begin try 
                  auto_cleanup (fun () ->
                    matching_multiplicity (fun remaining_problems ->
                      if !rule_computed = 7644 then 
                        begin
                          Printf.printf "After matching multiplicity\n";
                          display_remaining_problems remaining_problems;
                          flush_all ()
                        end;
                      matching_variables (fun () -> 
                        let (subst',context') = match var_context.v_link with
                          | NoLink ->
                              (* The matching was strict *)
                              let subst = 
                                List.map (fun v -> match v.v_link with 
                                  | FTLink t -> (v,t)
                                  | _ -> failwith "[exists_matching_multiplicity] Unexpected case"
                                ) !current_bound_vars
                              in
                              subst,context
                          | FTLink t ->
                              (* The matching was not strict *)
                              let subst = 
                                List.map (fun v -> match v.v_link with 
                                  | FTLink t -> (v,t)
                                  | _ -> failwith "[exists_matching_multiplicity] Unexpected case"
                                ) !current_bound_vars
                              in
                              begin match t with
                              | FAC(g,args) when f == g -> 
                                  let context' t' = context (FAC(f,add f t' args)) in
                                  subst,context'
                              | _ ->
                                  let context' t' = context (FAC(f,add f t' [t,1])) in
                                  subst,context'
                              end
                          | _ -> failwith "Wrong link"
                        in
                        Some (context',subst')
                      ) remaining_problems
                    ) [] false f args1 args2
                  )
                with NoMatch -> 
                  go_through_position_list_multiplicity f (fun args' -> context (FAC(f,args'))) args2
                end
            | _ ->
                match matching_one t1 sub_t2 with 
                | Some subst -> Some (context,subst)
                | None -> go_through_position_list_multiplicity f (fun args' -> context (FAC(f,args'))) args2

      and go_through_position_list context = function
        | [] -> None
        | t::q -> 
            match go_through_position (fun t' -> context (t'::q)) t with
            | None -> go_through_position_list (fun args' -> context (t :: args')) q
            | res -> res
  
      and go_through_position_list_multiplicity f context = function
        | [] -> None
        | (t,1)::q ->
            begin match go_through_position (fun t' -> context (add f t' q)) t with
            | None -> go_through_position_list_multiplicity f (fun args' -> context (add f t args')) q
            | res -> res
            end
        | (t,k)::q ->
            match go_through_position (fun t' -> context (add f t' ((t,k-1)::q))) t with
            | None -> go_through_position_list_multiplicity f (fun args' -> context (add_multiplicity f t k args')) q
            | res -> res
      in
  
      go_through_position (fun t -> t) t2 

  end

  let is_root f = function
    | FFunc(g,_),_ -> f == g
    | FAC(g,_),_ -> f == g
    | _ -> false 

  let rec split_by_root_symbol acc f = function
    | ((FFunc(g,_) | FAC(g,_)),_) as t :: q when f == g -> split_by_root_symbol (t::acc) f q
    | l -> acc, l

  let rec check_bounded_variables_one t k = function
    | [] -> raise NoMatch
    | (t',k')::q ->
        match compare t t' with
        | 0 -> 
            if k < k'
            then (t',k'-k)::q
            else if k = k'
            then q
            else raise NoMatch
        | 1 -> (t',k') :: check_bounded_variables_one t k q
        | _ -> raise NoMatch

  let rec check_bounded_variables bound_found f vars1 list2 = match vars1 with
    | [] -> [],list2
    | (FVar { v_link = FTLink t; _ },k) :: q -> 
        begin match t with 
        | FAC(g,args) when f == g ->
          let list2' = 
            List.fold_left (fun acc_list2 (u,n) ->
              check_bounded_variables_one u (k*n) acc_list2
            ) list2 args 
          in
          bound_found := true;
          check_bounded_variables bound_found f q list2'
        | _ -> 
          let list2' = check_bounded_variables_one t k  list2 in
          bound_found := true;
          check_bounded_variables bound_found f q list2'
        end
    | (FVar v,k) ::q -> 
        let vars1',list2' = check_bounded_variables bound_found f q list2 in
        (FVar v,k) :: vars1', list2'
    | _ -> failwith "[check_bounded_variables] Unexpected term"
      
  let rec matching_unique remaining_ref t1 t2 = match t1, t2 with
    | FVar { v_link = FTLink t1'; _ }, _ -> if not (equal t1' t2) then raise NoMatch
    | FVar v, _ -> link v (FTLink t2)
    | _, FVar _ -> raise NoMatch
    | FFunc(f1,args1), FFunc(f2,args2) -> 
        if f1 != f2 then raise NoMatch;
        List.iter2 (matching_unique remaining_ref) args1 args2
    | FAC(f1,args1), FAC(f2,args2) ->
        if f1 != f2 then raise NoMatch;
        let count_term1 = List.fold_left (fun acc (_,k) -> k + acc) 0 args1 in
        let count_term2 = List.fold_left (fun acc (_,k) -> k + acc) 0 args2 in
        if count_term1 > count_term2 then raise NoMatch;
        matching_multiplicity remaining_ref f1 [] [] args1 args2
    | _ -> raise NoMatch

  and matching_multiplicity remaining_ref f prev1 prev2 list1 list2 = match list1, list2 with 
    | (((FFunc(f1,_) | FAC(f1,_)) as t1,k1) as mt1) :: q1, ((((FFunc(f2,_) | FAC(f2,_)) as t2), k2) as mt2) :: q2 ->
        begin match compare_symbol f1 f2 with 
        | -1 -> raise NoMatch
        | 1 ->  matching_multiplicity remaining_ref f prev1 ((t2,k2)::prev2) list1 q2
        | _ ->
            if q2 = [] || not (is_root f2 (List.hd q2))
            then 
              if k1 > k2
              then raise NoMatch
              else
                begin 
                  matching_unique remaining_ref t1 t2;
                  if k1 = k2
                  then matching_multiplicity remaining_ref f prev1 prev2 q1 q2
                  else matching_multiplicity remaining_ref f prev1 prev2 q1 ((t2,k2-k1)::q2)
                end
            else
              let prev1', list_rest1 = split_by_root_symbol (mt1::prev1) f1 q1 in
              let prev2', list_rest2 = split_by_root_symbol (mt2::prev2) f2 q2 in
              matching_multiplicity remaining_ref f prev1' prev2' list_rest1 list_rest2
        end
    | ((FFunc _ | FAC _),_)::_, _-> raise NoMatch
    | _ -> 
        let new_list2 = List.rev_append prev2 list2 in
        match prev1 = [] && list1 = [], new_list2 = [] with
        | true, false
        | false, true -> raise NoMatch
        | false, false -> remaining_ref := (f, prev1,list1, new_list2) :: !remaining_ref
        | _ -> ()

  let matching limit t1 t2 = 
    auto_cleanup (fun () ->
      try 
        let remaining_ref = ref [] in
        matching_unique remaining_ref t1 t2;
        
        let rec explore_remaining prev_remaining = function
          | [] -> ()
          | (f,rev_others1,vars1,list2) as data :: q ->
              let found_bound = ref false in
              let (new_vars1,new_list2) = check_bounded_variables found_bound f vars1 list2 in
              if !found_bound
              then 
                begin 
                  let new_t1 = FAC(f,List.rev_append rev_others1 new_vars1) in
                  let new_t2 = FAC(f,new_list2) in
                  remaining_ref := List.rev_append prev_remaining q;
                  matching_unique remaining_ref new_t1 new_t2;
                  explore_remaining [] !remaining_ref
                end
              else explore_remaining (data::prev_remaining) q

        in
        
        explore_remaining [] !remaining_ref;

        if !remaining_ref = []
        then 
          let subst = 
            List.map (fun x -> match x.v_link with
              | FTLink t -> (x,t)
              | _ -> failwith "Unexpected link"
            ) !current_bound_vars
          in
          [subst]
        else
          let eq_list1= 
            List.fold_left (fun acc (f,rev_others1,vars1,list2) ->
              let new_t1 = FAC(f,List.rev_append rev_others1 vars1) in
              let new_t2 = FAC(f,list2) in
              (new_t1,new_t2)::acc
            ) [] !remaining_ref
          in
          let eq_list2 = 
            List.fold_left (fun acc x -> match x.v_link with
              | FTLink t -> (FVar x,t)::acc
              | _ -> failwith "Unexpected link"
            ) eq_list1 !current_bound_vars
          in
          maude_matching limit eq_list2
      with NoMatch -> []
    )

  let matching_one t1 t2 = match matching (Some 1) t1 t2 with 
    | [] -> None
    | [subst] -> Some subst
    | _ -> failwith "[matching_one] Unexpected number of substitutions."

  let matching_one = Basic.matching_one

  let exists_matching pred t1 t2 = 
    let slist = matching None t1 t2 in
    List.exists pred slist

  (* let exists_matching pred t1 t2 = 
    Statistic.record_notail Statistic.time_exists_matching (fun () -> exists_matching pred t1 t2) *)
  
  let exists_matching = Basic.exists_matching

  (* let exists_matching pred t1 t2 = 
    print_string "exists_matching\n";
    flush_all ();
    let r = Basic.exists_matching pred t1 t2 in
    print_string "end\n";
    flush_all ();
    r *)

  (* let exists_matching pred t1 t2 = 
    let r1 = Basic.exists_matching pred t1 t2 in
    let r2 = exists_matching pred t1 t2 in
    if r1 <> r2 
    then 
      begin 
        Printf.printf "** exists_matching %s with %s\n" (string_of_term t1) (string_of_term t2);
        failwith "Error"
      end;
    r1 *)

  let find_matching_term_list list1 list2 = 
    let r1 = Basic.find_matching_term_list list1 list2 in
    (* let eq_list = List.combine list1 list2 in
    let r2 = maude_matching (Some 1) eq_list in
    begin match r1, r2 with
    | None, [] -> ()
    | Some _, [_] -> ()
    | None, [subst] -> 
        Printf.printf "*** Discrepenticy in matching function (Maude find one but not Native)\n";
        Printf.printf "- Matching problem: %s\n"
          (string_of_list (fun (t1,t2) -> Printf.sprintf "%s -> %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
        Printf.printf "- Substitution found by Maude: %s\n" (string_of_subst subst);
        failwith "Error"
    | Some subst, [] ->
        Printf.printf "*** Discrepenticy in matching function (Native find one but not Maude)\n";
        Printf.printf "- Matching problem: %s\n"
          (string_of_list (fun (t1,t2) -> Printf.sprintf "%s -> %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
        Printf.printf "- Substitution found by Native: %s\n" (string_of_subst subst);
        failwith "Error"
    | _ -> failwith "[find_matching_term_list] This case should not happen."
    end; *)
    r1

  (* Matching with context : C[u\sigma] =_AC v *)

  let exists_matching_with_context pred t1 t2 =
    let x = FVar (Term.fresh_variable ()) in

    let rec go_through_position context sub_t2 = match sub_t2 with
      | FVar _ ->
          let slist = matching None  t1 sub_t2 in
          List.exists (pred context) slist
      | FFunc(f,args) ->
          let slist = matching None t1 sub_t2 in
          List.exists (pred context) slist ||
          go_through_position_list (fun args' -> context (FFunc(f,args'))) args
      | FAC(f,args) ->
          let slist = matching None t1 sub_t2 in
          if List.exists (pred context) slist
          then true
          else
            let test_more = match t1 with
              | FVar _ -> true
              | FAC(g,_) -> f == g
              | _ -> false
            in
            let additional_result = 
              if test_more
              then 
                let new_t1 = FAC(f,add f t1 [(x,1)]) in
                let slist' = matching None new_t1 sub_t2 in
                List.exists (fun subst ->
                  let t = apply_subst subst x in
                  match t with
                  | FAC(g1,args1) when f == g1 -> pred (fun t' -> context (FAC(f,add f t' args1))) subst
                  | _ -> pred (fun t' -> context (FAC(f,add f t' [t,1]))) subst
                ) slist'
              else false
            in
            if additional_result
            then true
            else go_through_position_list_multiplicity f (fun args' -> context (FAC(f,args'))) args
    
    and go_through_position_list context = function
      | [] -> false
      | t::q -> 
          go_through_position (fun t' -> context (t'::q)) t ||
          go_through_position_list (fun args' -> context (t :: args')) q

    and go_through_position_list_multiplicity f context = function
      | [] -> false
      | (t,1)::q ->
          go_through_position (fun t' -> context (add f t' q)) t ||
          go_through_position_list_multiplicity f (fun args' -> context (add f t args')) q
      | (t,k)::q ->
          go_through_position (fun t' -> context (add f t' ((t,k-1)::q))) t ||
          go_through_position_list_multiplicity f (fun args' -> context (add_multiplicity f t k args')) q
    in

    go_through_position (fun t -> t) t2 

  let exists_matching_with_context = Basic.exists_matching_with_context

  let matching_with_context_one t1 t2 = 
    let x = FVar (Term.fresh_variable ()) in
  
    let rec go_through_position context sub_t2 = match sub_t2 with
      | FVar _ -> 
          let* subst = matching_one t1 sub_t2 in
          Some(context,subst)
      | FFunc(f,args) ->
          begin match matching_one t1 sub_t2 with
          | Some subst -> Some (context,subst)
          | None -> go_through_position_list (fun args' -> context (FFunc(f,args'))) args
          end
      | FAC(f,args) ->
          match matching_one t1 sub_t2 with
          | Some subst -> Some (context,subst)
          | None -> 
              let test_more = match t1 with
                | FVar _ -> true
                | FAC(g,_) -> f == g
                | _ -> false
              in
              let additional_result = 
                if test_more
                then 
                  let new_t1 = FAC(f,add f t1 [(x,1)]) in
                  let* subst = matching_one new_t1 sub_t2 in
                  let t = apply_subst subst x in
                  match t with
                  | FAC(g1,args1) when f == g1 -> Some ((fun t' -> context (FAC(f,add f t' args1))),subst)
                  | _ -> Some((fun t' -> context (FAC(f,add f t' [t,1]))),subst)
                else None
              in
              match additional_result with
              | None -> go_through_position_list_multiplicity f (fun args' -> context (FAC(f,args'))) args
              | res -> res
          
    and go_through_position_list context = function
      | [] -> None
      | t::q -> 
          match go_through_position (fun t' -> context (t'::q)) t with
          | None -> go_through_position_list (fun args' -> context (t :: args')) q
          | res -> res

    and go_through_position_list_multiplicity f context = function
      | [] -> None
      | (t,1)::q ->
          begin match go_through_position (fun t' -> context (add f t' q)) t with
          | None -> go_through_position_list_multiplicity f (fun args' -> context (add f t args')) q
          | res -> res
          end
      | (t,k)::q ->
          match go_through_position (fun t' -> context (add f t' ((t,k-1)::q))) t with
          | None -> go_through_position_list_multiplicity f (fun args' -> context (add_multiplicity f t k args')) q
          | res -> res
    in

    go_through_position (fun t -> t) t2 

  (* let matching_with_context_one t1 t2 = 
    Statistic.record_notail Statistic.time_matching_with_context_one (fun () -> matching_with_context_one t1 t2) *)
  
  let matching_with_context_one = Basic.matching_with_context_one

  (* let matching_with_context_one t1 t2 = 
    print_string "matching_with_context_one\n";
    flush_all ();
    let r = Basic.matching_with_context_one t1 t2 in
    print_string "end\n";
    flush_all ();
    r *)


  (* let matching_with_context_one t1 t2 = match Basic.matching_with_context_one t1 t2 with 
    | None -> 
        if matching_with_context_one t1 t2 <> None
        then 
          begin 
            Printf.printf "** Matching_with_context_one %s with %s\n" (string_of_term t1) (string_of_term t2);
            failwith "Error"
          end;
        None
    | Some(context,subst) ->
        let t1' = context (apply_subst subst t1) in
        if not (equal t1' t2)
        then 
          begin 
            Printf.printf "** Matching_with_context_one %s with %s\n" (string_of_term t1) (string_of_term t2);
            Printf.printf "result:\ncontext = %s\nsubst: %s\napplied: %s\nt1': %s\n" (string_of_term (context (of_term hole))) (string_of_subst subst) (string_of_term (apply_subst subst t1)) (string_of_term t1');
            failwith "Error"
          end;
        Some(context,subst) *)
    
      

  (********************
      Subterm 
  *********************)

  let rec is_subterm_syntactic u t = match t with
    | FVar _ -> equal u t
    | FFunc(_,args) -> equal u t || List.exists (is_subterm_syntactic u) args
    | FAC(_,args) -> List.exists (fun (t,_) -> is_subterm_syntactic u t) args
  
  let rec is_subterm_AC_multiplicity list1 list2 = match list1, list2 with 
    | [], _ -> true
    | _, [] -> false
    | (t1,k1)::q1, (t2,k2)::q2 ->
        match compare t1 t2 with
        | -1 -> false 
        | 0 -> k1 <= k2 && is_subterm_AC_multiplicity q1 q2
        | _ -> is_subterm_AC_multiplicity list1 q2
  
  let rec is_subterm_AC f args_ac v = match v with
    | FVar _ -> false
    | FFunc(_,args) -> List.exists (is_subterm_AC f args_ac) args
    | FAC(g,args) when f != g -> List.exists (fun (v',_) -> is_subterm_AC f args_ac v') args
    | FAC(_,args) ->
        is_subterm_AC_multiplicity args_ac args ||
        List.exists (fun (v',_) -> is_subterm_AC f args_ac v') args

  let is_subterm u v = match u with
    | FVar x -> occurs x v 
    | FFunc _ -> is_subterm_syntactic u v
    | FAC(f,args) -> is_subterm_AC f args v

  (* let is_subterm u v = 
    Statistic.record_notail Statistic.time_subterm (fun () -> is_subterm u v) *)
end
