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

open Term 
open Flattened
open AC

type ac_data = 
  {
    ac_symb : symbol;
    ac_left_arg : Flattened.term;
    ac_right_arg : Flattened.term
  }

type recorded_term =
  {
    term : term;
    flattened: Flattened.term;
    ac_data_op: ac_data option
  }

type rewrite_rule =
  {
    lhs : recorded_term;
    rhs : recorded_term
  }



type rewriting_system = rewrite_rule list

let verbose_unifiers = ref false
let verbose_flattened = ref false
let verbose_loop = ref false
let verbose_normalisation = ref false
let verbose_augmented_R = ref false

let verbose_everyrule = ref false
let pretty = ref true

let convergent = ref false
let order_strong_computable = ref true
let update_Rn = ref true

let extended_subsume = ref false

(*************************************
  Pretty/Standard display functions 
**************************************)

let rec pretty_term acc_i = function 
  | Var { v_link = VLink v'; _ } -> Var v'
  | Var v -> 
      let v' = { v_name = "_"; v_id = !acc_i; v_link = NoLink } in
      incr acc_i;
      link v (VLink v');
      Var v'
  | Func(f,args) -> Func(f,List.map (pretty_term acc_i) args)

let pretty_string_of_rewrite_rule rw_rule = 
  let vars = 
    auto_cleanup (fun () ->
      get_variables rw_rule.lhs.term;
      get_variables rw_rule.rhs.term;
      !current_bound_vars
    )
  in

  let vars_sorted = List.sort compare_variable vars in

  auto_cleanup (fun () ->
    let acc_i = ref 1 in
    List.iter (fun v ->
      let v' = { v_name = "_"; v_id = !acc_i; v_link = NoLink } in
      incr acc_i;
      link v (VLink v')
    ) vars_sorted;

    if !verbose_flattened
    then 
      let ft_lhs = Flattened.apply_renaming_preserving_compare rw_rule.lhs.flattened in
      let ft_rhs = Flattened.apply_renaming_preserving_compare rw_rule.rhs.flattened in
      Printf.sprintf "%s -> %s" (Flattened.string_of_term ft_lhs) (Flattened.string_of_term ft_rhs)
    else
      let t_lhs = apply_renaming rw_rule.lhs.term in
      let t_rhs = apply_renaming rw_rule.rhs.term in
      Printf.sprintf "%s -> %s" (string_of_term t_lhs) (string_of_term t_rhs)
  )

let string_of_rewrite_rule rw_rule =
  if !pretty 
  then pretty_string_of_rewrite_rule rw_rule
  else
    if !verbose_flattened
    then Printf.sprintf "%s -> %s" (Flattened.string_of_term rw_rule.lhs.flattened) (Flattened.string_of_term rw_rule.rhs.flattened)
    else Printf.sprintf "%s -> %s" (string_of_term rw_rule.lhs.term) (string_of_term rw_rule.rhs.term)

let pretty_string_of_equation (l,r) = 
  auto_cleanup (fun () ->
    let acc_i = ref 1 in
    let l' = pretty_term acc_i l in
    let r' = pretty_term acc_i r in 
    Printf.sprintf "%s = %s" (string_of_term l') (string_of_term r')
  )

let string_of_equation (l,r) = 
  if !pretty
  then pretty_string_of_equation (l,r)
  else Printf.sprintf "%s = %s" (string_of_term l) (string_of_term r)

(*************************************
  Useful functions
**************************************)

(** Transformations *)

let reverse rw_rule = { lhs = rw_rule.rhs; rhs = rw_rule.lhs }

let recorded_term_of_term t = match t with 
  | Func(f,[t1;t2]) when f.f_cat = AC ->
      let ft1 = Flattened.of_term t1 in
      let ft2 = Flattened.of_term t2 in
      let data_op = Some { ac_symb = f; ac_left_arg = ft1; ac_right_arg = ft2 } in
      { term = t; flattened = Flattened.apply_symbol f [ft1;ft2]; ac_data_op = data_op }
  | Func(f,_) when f.f_cat = AC -> failwith "[recorded_term_of_term] Wrong arity."
  | _ -> { term = t; flattened = Flattened.of_term t; ac_data_op = None }

let recorded_term_of_flattened_term ft = match ft with
  | Flattened.FVar _
  | Flattened.FFunc _ -> { term = Flattened.to_term ft; flattened = ft; ac_data_op = None }
  | Flattened.FAC(f,[(t,2)]) ->
      let ft_left = t in
      let ft_right = t in
      let ac_data = { ac_symb = f; ac_left_arg = ft_left; ac_right_arg = ft_right } in
      { term = Flattened.to_term ft; flattened = ft; ac_data_op = Some ac_data }
  | Flattened.FAC(f,[(t,1);(t',1)]) ->
      let ft_left = t in
      let ft_right = t' in
      let ac_data = { ac_symb = f; ac_left_arg = ft_left; ac_right_arg = ft_right } in
      { term = Flattened.to_term ft; flattened = ft; ac_data_op = Some ac_data }
  | Flattened.FAC(f,(t,1)::q) ->
      let ft_left = t in
      let ft_right = Flattened.FAC(f,q) in
      let ac_data = { ac_symb = f; ac_left_arg = ft_left; ac_right_arg = ft_right } in
      { term = Flattened.to_term ft; flattened = ft; ac_data_op = Some ac_data }
  | Flattened.FAC(f,(t,k)::q) ->
      let ft_left = t in
      let ft_right = Flattened.FAC(f,(t,k-1)::q) in
      let ac_data = { ac_symb = f; ac_left_arg = ft_left; ac_right_arg = ft_right } in
      { term = Flattened.to_term ft; flattened = ft; ac_data_op = Some ac_data }
| Flattened.FAC(_,[]) -> failwith "[recorded_term_of_flattened_term] Unexpected case."

(** Refreshing *)

let refresh_ac_data data = 
  { data with 
    ac_left_arg = Flattened.refresh_no_cleanup data.ac_left_arg; 
    ac_right_arg = Flattened.refresh_no_cleanup data.ac_right_arg
  }
let refresh_recorded_term rt = 
  let data_op = match rt.ac_data_op with
    | None -> None
    | Some d -> Some (refresh_ac_data d)
  in

  { 
    term = refresh_term rt.term; 
    flattened = Flattened.refresh_no_cleanup rt.flattened;
    ac_data_op = data_op
  }

let refresh_rewrite_rule rw_rule = 
  let vars = 
    auto_cleanup (fun () ->
      get_variables rw_rule.lhs.term;
      get_variables rw_rule.rhs.term;
      !current_bound_vars
    )
  in

  let vars_sorted = List.sort compare_variable vars in

  auto_cleanup (fun () ->
    List.iter (fun v ->
      link v (VLink (fresh_variable ()))  
    ) vars_sorted;
    { lhs = refresh_recorded_term rw_rule.lhs; rhs = refresh_recorded_term rw_rule.rhs }
  )

(*************************************
  Main functions
**************************************)

(** Checking convergence *)

let apply_one_rewrite_rule rw_rule t = 
  let found_one = ref false in
  
  let rec explore_term t = match t with 
    | Var _ -> t
    | Func(f,args) ->
        let t_flat = Flattened.of_term t in
        match Flattened.matching_one rw_rule.lhs.flattened t_flat with
        | None -> Func(f,List.map explore_term args)
        | Some subst_flat ->
            let subst = List.map (fun (x,u) -> x, Flattened.to_term u) subst_flat in
            found_one := true;
            apply_subst subst rw_rule.rhs.term
  in

  let t' = explore_term t in
  if !found_one 
  then Some t'
  else None
  
let apply_all_rewrite_rules rw_rules t = 
  
  let rec try_rules t = function
    | [] -> t
    | rw_rule::q ->
        match apply_one_rewrite_rule rw_rule t with
        | None -> try_rules t q
        | Some t' -> try_rules t' rw_rules
  in

  try_rules t rw_rules


let explore_critical_pair rw_rules rw_rule1 rw_rule2 = 
  
  let rec explore_rule2 lhs2 context = match lhs2 with
    | Var _ -> ()
    | Func(f,args) ->
        let subst_list = AC.unify rw_rule1.lhs.term lhs2 in
        let term1 = context rw_rule1.rhs.term in

        List.iter (fun subst ->
          let new_term1 = apply_subst subst term1 in
          let new_term2 = apply_subst subst rw_rule2.rhs.term in

          let t1' = apply_all_rewrite_rules rw_rules new_term1 in
          let t2' = apply_all_rewrite_rules rw_rules new_term2 in
          if not (Flattened.equal (Flattened.of_term t1') (Flattened.of_term t2'))
          then 
            begin 
              Printf.printf "Critical pair: %s and %s\n" (string_of_term new_term1) (string_of_term new_term2);
              Printf.printf "Rule 1 : %s\n" (string_of_rewrite_rule rw_rule1);
              Printf.printf "Rule 2 : %s\n" (string_of_rewrite_rule rw_rule2);
              Printf.printf "Subterm of Rule 2 : %s\n" (string_of_term lhs2);
              Printf.printf "Subst : %s\n" (string_of_subst subst);
              raise Not_found
            end
        ) subst_list;

        let rec creating_context prev_args = function 
          | [] -> ()
          | t::q ->
              let context' t' = context (Func(f,List.rev_append prev_args (t'::q))) in
              explore_rule2 t context';
              creating_context (t::prev_args) q
        in

        creating_context [] args
  in

  explore_rule2 rw_rule2.lhs.term (fun x -> x)


let check_convergence rw_rules =
  let rw_rules1 = List.map refresh_rewrite_rule rw_rules in
  let rw_rules2 = List.map refresh_rewrite_rule rw_rules in
  try 
    List.iter (fun rw_rule1 ->
      List.iter (fun rw_rule2 ->
        explore_critical_pair rw_rules rw_rule1 rw_rule2 
      ) rw_rules1
    ) rw_rules2;
    true
  with Not_found -> false



(** Applying normalisation steps *)

let rec one_rewrite_step rwsys ft = 
  if not (Flattened.check_well_sorted ft)
  then 
    begin 
      Printf.printf "one_rewrite_step = ";
      Flattened.display_term ft;
      print_string "\n";
      failwith "Not well sorted"
    end;
  (* if !rule_computed = 185443 then 
    begin
      Printf.printf "one_rewrite_step = ";
      Flattened.display_term ft;
      print_string "\n";
      flush_all ()
    end; *)
  let r = match rwsys with
  | [] -> None
  | rw_rule :: q ->
      (* if !rule_computed = 185443 then 
        begin
          Printf.printf "rewrite rule = %s\n" (string_of_rewrite_rule rw_rule);
          flush_all ()
        end; *)
      match Flattened.matching_with_context_one rw_rule.lhs.flattened ft with
      | None -> 
          (* if !rule_computed = 185443 then 
          begin
            Printf.printf "Result = None\n";
            flush_all ()
          end; *)
          one_rewrite_step q ft
      | Some(context,subst) ->
          (* if !rule_computed = 185443 then 
            begin
              Printf.printf "Result = Some with\n  Context = %s\n  Subst = %sn" (Flattened.string_of_term (context (Flattened.of_term hole))) (Flattened.string_of_subst subst);
              flush_all ()
            end; *)
          let ft' = context (Flattened.apply_subst subst rw_rule.rhs.flattened) in
          (* if !rule_computed = 185443 then 
            begin
              Printf.printf "Result = Some with\n  Context = %s\n  Subst = %s\n  New term: %s\n" (Flattened.string_of_term (context (Flattened.of_term hole))) (Flattened.string_of_subst subst) (Flattened.string_of_term ft');
              flush_all ()
            end; *)
          Some ft'
  in
  begin match r with 
  | None -> ()
  | Some ft -> 
    if not (Flattened.check_well_sorted ft)
      then 
        begin 
          Printf.printf "one_rewrite_step END = ";
          Flattened.display_term ft;
          print_string "\n";
          failwith "Not well sorted"
        end
  end;
  r
          
let rec rewrite_steps_aux rwsys ft = 
  if not (Flattened.check_well_sorted ft)
    then 
      begin 
        Printf.printf "rewrite_steps_aux = ";
        Flattened.display_term ft;
        print_string "\n";
        failwith "Not well sorted"
      end;
  (* if !rule_computed = 185443
    then 
      begin 
        print_string "rewrite_steps_aux\n";
        flush_all ()
      end; *)
  match one_rewrite_step rwsys ft with
  | None -> ft
  | Some ft' -> rewrite_steps_aux rwsys ft'

let rewrite_steps_flattened rwsys ft = 
  if not (Flattened.check_well_sorted ft)
    then 
      begin 
        Printf.printf "rewrite_steps_flattened = ";
        Flattened.display_term ft;
        print_string "\n";
        failwith "Not well sorted"
      end;
  (* if !rule_computed = 185443 then 
    begin
      Printf.printf "rewrite_steps_flattened = ";
      Flattened.display_term ft;
      print_string "\n";
      flush_all ()
    end; *)
  
  match one_rewrite_step rwsys ft with
  | None -> None
  | Some ft -> Some (rewrite_steps_aux rwsys ft)

let rewrite_steps_recorded_term rwsys rt = match rewrite_steps_flattened rwsys rt.flattened with
  | None -> None
  | Some ft -> Some (recorded_term_of_flattened_term ft)

(** Applying normalisation steps on left hand side of a rewrite rule before addition *)

(** We assume here that lhs > rhs by Order.compare_strong. We simplify the left hand side until
    either lhs > rhs does not hold or no more normalisation is possible. Returns None is the 
    resulting rule has the same lhs and rhs *)
let rec simplify_lhs_rw_rule rwsys rw_rule = match one_rewrite_step rwsys rw_rule.lhs.flattened with
  | None -> Some rw_rule
  | Some lhs_ft ->
      match Order.compare_strong rw_rule.rhs.flattened lhs_ft with
      | Eq -> None
      | Unknown -> Some rw_rule
      | Less -> simplify_lhs_rw_rule rwsys { rw_rule with lhs = recorded_term_of_flattened_term lhs_ft }

(* The normalisation rules *)

let rule_Var rw_rule =
  let dvars = Flattened.diff_variables rw_rule.rhs.flattened rw_rule.lhs.flattened in
  if dvars = []
  then None
  else 
    let subst = List.map (fun x -> (x,Func(!Term.amin,[]))) dvars in
    let subst_ft = List.map (fun x -> (x,Flattened.FFunc(!Term.amin,[]))) dvars in

    let ft', data_op = match rw_rule.rhs.ac_data_op with
      | None -> Flattened.apply_subst subst_ft rw_rule.rhs.flattened, None
      | Some data -> 
          let left = Flattened.apply_subst subst_ft data.ac_left_arg in
          let right = Flattened.apply_subst subst_ft data.ac_right_arg in
          let ft = Flattened.apply_symbol data.ac_symb [left;right] in
          ft, Some 
            { data with 
              ac_left_arg = Flattened.apply_subst subst_ft data.ac_left_arg;
              ac_right_arg = Flattened.apply_subst subst_ft data.ac_right_arg;
            }
    in

    let _ = if not (Flattened.check_well_sorted ft')
      then 
        begin 
          Printf.printf "rule_Var = ";
          Flattened.display_term ft';
          print_string "\n";
          failwith "Not well sorted"
        end
    in

    let t' = Term.apply_subst subst rw_rule.rhs.term in 
    let rt' = { term = t'; flattened = ft'; ac_data_op = data_op } in

    let rule1 = { rw_rule with rhs = rt' } in
    let rule2 = { lhs = rw_rule.rhs; rhs = rt' } in
    Some [rule1;rule2]

let rule_NormR_NormL rwsysRn rw_rule = 

  let r_changed = ref false in

  let rhs_rt = match rewrite_steps_recorded_term rwsysRn rw_rule.rhs with
    | None -> rw_rule.rhs
    | Some rt -> r_changed := true; rt
  in

  match rw_rule.lhs.ac_data_op with 
  | None ->
      (* Case of FVar of FFunc *)
      begin match rw_rule.lhs.flattened with
      | FVar _ -> if !r_changed then Some [ { rw_rule with rhs = rhs_rt }] else None
      | FFunc(f,args) ->
          let l_changed = ref false in
          let args' = 
            List.map (fun s_i -> match rewrite_steps_flattened rwsysRn s_i with
              | None -> s_i
              | Some s_i' -> l_changed := true; s_i'
            ) args in
          if !l_changed 
          then 
            begin
              let ft = Flattened.FFunc(f,args') in
              let _ = if not (Flattened.check_well_sorted ft)
                then 
                  begin 
                    Printf.printf "rule_NormR_NormL = ";
                    Flattened.display_term ft;
                    print_string "\n";
                    failwith "Not well sorted"
                  end
              in
              let rt = recorded_term_of_flattened_term ft in

              if !convergent
              then 
                (* The initial equational theory has a convergent rewrite system *)
                Some [{ lhs = rt; rhs = rhs_rt }]
              else
                let rt' = match rewrite_steps_flattened rwsysRn ft with
                  | None -> rt
                  | Some ft' -> recorded_term_of_flattened_term ft'
                in
                let rule1 = { lhs = rt; rhs = rhs_rt } in
                let rule2 = { lhs = rhs_rt; rhs = rt' } in
                Some [rule1;rule2]
            end
          else if !r_changed
          then Some [ { rw_rule with rhs = rhs_rt }]
          else None 
      | FAC _ -> failwith "[rule_NormR_NormL] Unexpected case"
      end
  | Some data ->
      let l_changed = ref false in
      let rewrite ft = match rewrite_steps_flattened rwsysRn ft with
        | None -> ft
        | Some ft' -> l_changed := true; ft'
      in

      let left = rewrite data.ac_left_arg in
      (* let _ = 
        if !rule_computed = 185443 then begin
        Printf.printf "rule_NormR_NormL (5'') %s\n" (Flattened.string_of_term data.ac_right_arg);
        Printf.printf "right before rewrite = "; Flattened.display_term data.ac_right_arg; print_string "\n";
        flush_all ()end
      in *)

      

      let right = rewrite data.ac_right_arg in
      (* if !rule_computed = 185443
      then begin 
        Printf.printf "left = "; Flattened.display_term left; print_string "\n";
        Printf.printf "right = "; Flattened.display_term right; print_string "\n";
        Printf.printf "End Rewrite\n";
      flush_all ()
      end; *)

      if !l_changed 
      then 
        begin
          (* let _ = 
            if !rule_computed = 185443 then begin
            Printf.printf "l_changed\n";
            flush_all ()end
          in *)
          let ft = Flattened.apply_symbol data.ac_symb [left;right] in
          let _ = if not (Flattened.check_well_sorted ft)
            then 
              begin 
                Printf.printf "rule_NormR_NormL2 = ";
                Flattened.display_term ft;
                print_string "\n";
                failwith "Not well sorted"
              end
          in
          (* let _ = 
            if !rule_computed = 185443 then begin
            Printf.printf "after apply_symbol\n";
            flush_all ()end
          in *)
          let data_op = Some { data with ac_left_arg = left; ac_right_arg = right } in
          let t = Func(data.ac_symb,[Flattened.to_term left;Flattened.to_term right]) in
          (* let _ = 
            if !rule_computed > 184800 then begin
            Printf.printf "after to_term\n";
            flush_all ()end
          in *)
          let rt = { term = t; flattened = ft; ac_data_op = data_op } in

          (* let _ = 
            if !rule_computed > 184800 then begin
            Printf.printf "before IF\n";
            flush_all ()end
          in *)

          if !convergent
          then 
            (* The initial equational theory has a convergent rewrite system *)
            Some [{ lhs = rt; rhs = rhs_rt }]
          else
            let rt' = match rewrite_steps_flattened rwsysRn ft with
              | None -> rt
              | Some ft' -> recorded_term_of_flattened_term ft'
            in
            (* let _ = 
              if !rule_computed = 185443 then begin
              Printf.printf "After rt'\n";
              flush_all ()end
            in *)

            let rule1 = { lhs = rt; rhs = rhs_rt } in
            let rule2 = { lhs = rhs_rt; rhs = rt' } in
            Some [rule1;rule2]
        end
      else if !r_changed
      then Some [ { rw_rule with rhs = rhs_rt }]
      else None 

let rec normalise f rwsysRn rw_rule = match rule_NormR_NormL rwsysRn rw_rule with
  | None -> 
      begin match rule_Var rw_rule with
      | None -> f (refresh_rewrite_rule rw_rule)
      | Some l -> List.iter (normalise f rwsysRn) l
      end
  | Some norm_rules ->
      List.iter (fun rw -> match rule_Var rw with
        | None -> f rw
        | Some l -> List.iter (normalise f rwsysRn) l
      ) norm_rules

let normalise f rwsysRn rw_rule =
  if !verbose_normalisation
  then 
    normalise (fun rw ->
      Printf.printf "** Rule %s was normalised into %s\n" (pretty_string_of_rewrite_rule rw_rule) (pretty_string_of_rewrite_rule rw); 
      flush_all ();
      f rw
    ) rwsysRn rw_rule
  else normalise f rwsysRn rw_rule

let subsumes rw_rule_gen rw_rule_ins = 
  Flattened.exists_matching_with_context (fun context subst ->
    let ft = context (Flattened.apply_subst subst rw_rule_gen.rhs.flattened) in
    let _ = if not (Flattened.check_well_sorted ft)
      then 
        begin 
          Printf.printf "subsumes = ";
          Flattened.display_term ft;
          print_string "\n";
          failwith "Not well sorted"
        end
    in
    Flattened.equal ft rw_rule_ins.rhs.flattened
  ) rw_rule_gen.lhs.flattened rw_rule_ins.lhs.flattened

let check_flattended str ft = 
  let ft' = Flattened.of_term (Flattened.to_term ft) in
  if not (Flattened.equal ft ft')
  then failwith (str^" [Check_flattened] "^Flattened.string_of_term ft)

type rewriting_rule_ext = 
  { rw : rewrite_rule; strict : bool }

type db_entry = 
  { rw_ext : rewriting_rule_ext; mutable active : bool }

type database = 
  {
    mutable rwsys_R : db_entry list;
    queue_R : rewriting_rule_ext Rule_queue.queue;
    mutable rule_inserted : int;
    mutable rule_computed : int;
    rwsysEn : rewrite_rule list;
    mutable rwsysRn : rewrite_rule list
  }

let subsume_norm database subst rw_rule_gen rw_rule_ins context =
  if !extended_subsume
  then
    begin 
    let lhs_gen =  Flattened.apply_subst subst rw_rule_gen.lhs.flattened in
    let rhs_gen =  Flattened.apply_subst subst rw_rule_gen.rhs.flattened in
    
    let comp = Order.compare_strong rhs_gen lhs_gen in
    if comp = Unknown
    then false
    else 
      let rhs_gen1 = context rhs_gen in
      let rhs_gen2 = rewrite_steps_aux database.rwsysRn rhs_gen1 in
      Flattened.equal rhs_gen2 rw_rule_ins.rhs.flattened
  end
  else false

let subsumes_strict database rw_rule_gen rw_rule_ins = 
  (* print_string "**** Strict subsubmes:\n";
  Printf.printf "Gen rule: %s\n" (pretty_string_of_rewrite_rule rw_rule_gen);
  Printf.printf "Ins rule: %s\n" (pretty_string_of_rewrite_rule rw_rule_ins); *)
  let r = 
  match rw_rule_gen.lhs.ac_data_op, rw_rule_ins.lhs.ac_data_op with
    | Some data_gen, Some data_ins when data_gen.ac_symb == data_ins.ac_symb ->
        (* Case one: Context is a hole and root symbol of rw_rule_gen.lhs and rw_rule_ins.lhs is AC *)
        Flattened.exists_matching (fun subst -> 
          let left_arg_gen' = Flattened.apply_subst subst data_gen.ac_left_arg in
          let _ = if not (Flattened.check_well_sorted left_arg_gen')
            then 
              begin 
                Printf.printf "subsumes_strict1 = ";
                Flattened.display_term left_arg_gen';
                print_string "\n";
                failwith "Not well sorted"
              end
          in
          let right_arg_gen' = Flattened.apply_subst subst data_gen.ac_right_arg in
          let _ = if not (Flattened.check_well_sorted right_arg_gen')
            then 
              begin 
                Printf.printf "subsumes_strict2 = ";
                Flattened.display_term right_arg_gen';
                print_string "\n";
                failwith "Not well sorted"
              end
          in
          Flattened.equal left_arg_gen' data_ins.ac_left_arg &&
          Flattened.equal right_arg_gen' data_ins.ac_right_arg &&
          (* The left hand side equality is strict so we now check with right hand side *)
          (
            Flattened.equal (Flattened.apply_subst subst rw_rule_gen.rhs.flattened) rw_rule_ins.rhs.flattened ||
            subsume_norm database subst rw_rule_gen rw_rule_ins (fun x -> x)
          )
        ) rw_rule_gen.lhs.flattened rw_rule_ins.lhs.flattened
        ||
        Flattened.exists_matching_with_context (fun context subst ->
          let context_all t = 
            let ft = context t in
            let _ = if not (Flattened.check_well_sorted ft)
              then 
                begin 
                  Printf.printf "subsumes_strict3 = ";
                  Flattened.display_term ft;
                  print_string "\n";
                  failwith "Not well sorted"
                end
            in
            Flattened.apply_symbol data_ins.ac_symb [ft;data_ins.ac_right_arg] 
          in
          let ft_all = context_all (Flattened.apply_subst subst rw_rule_gen.rhs.flattened) in
          Flattened.equal ft_all rw_rule_ins.rhs.flattened ||
          subsume_norm database subst rw_rule_gen rw_rule_ins context_all
        ) rw_rule_gen.lhs.flattened data_ins.ac_left_arg
        ||
        Flattened.exists_matching_with_context (fun context subst ->
          let context_all t = 
            let ft = context t in
            let _ = if not (Flattened.check_well_sorted ft)
              then 
                begin 
                  Printf.printf "subsumes_strict4 = ";
                  Flattened.display_term ft;
                  print_string "\n";
                  failwith "Not well sorted"
                end
            in
            Flattened.apply_symbol data_ins.ac_symb [data_ins.ac_left_arg;ft]
          in
          let ft_all = context_all (Flattened.apply_subst subst rw_rule_gen.rhs.flattened) in
          Flattened.equal ft_all rw_rule_ins.rhs.flattened ||
          subsume_norm database subst rw_rule_gen rw_rule_ins context_all
        ) rw_rule_gen.lhs.flattened data_ins.ac_right_arg
    | _ -> 
        Flattened.exists_matching_with_context (fun context subst ->
          let ft = context (Flattened.apply_subst subst rw_rule_gen.rhs.flattened) in
          let _ = if not (Flattened.check_well_sorted ft)
            then 
              begin 
                Printf.printf "subsumes_strict5 = ";
                Flattened.display_term ft;
                print_string "\n";
                failwith "Not well sorted"
              end
          in
          Flattened.equal ft rw_rule_ins.rhs.flattened ||
          subsume_norm database subst rw_rule_gen rw_rule_ins context
        ) rw_rule_gen.lhs.flattened rw_rule_ins.lhs.flattened
  in
  (* Printf.printf "Res = %b\n" r; *)
  flush_all ();
  r
   
(* Computation of overlapping rules *)

let overlap_rules f_next rw_rule1 rw_rule2 =

  let rec go_through_rhs1 context = function
    | Var _ -> ()
    | Func(f,args) as t ->
        let unifiers = AC.unify t rw_rule2.lhs.term in
        
        List.iteri (fun i subst ->
          let l3 = Term.apply_subst subst rw_rule1.lhs.term in
          let r3' = context rw_rule2.rhs.term in
          let r3 = Term.apply_subst subst r3' in
          let l3,r3 = auto_cleanup (fun () -> refresh_term l3, refresh_term r3)in
          let rw_rule3 = { lhs = recorded_term_of_term l3; rhs = recorded_term_of_term r3 } in
          f_next rw_rule3
        ) unifiers;

        go_through_rhs1_list (fun args' -> context (Func(f,args'))) args

  and go_through_rhs1_list context = function
    | [] -> ()
    | t::q ->
        go_through_rhs1 (fun t' -> context (t'::q)) t;
        go_through_rhs1_list (fun args' -> context (t::args')) q
  in

  go_through_rhs1 (fun t -> t) rw_rule1.rhs.term

(* let overlap_rules f_next rw_rule1 rw_rule2 = 
  Statistic.record_notail Statistic.time_overlap_rules (fun () -> overlap_rules f_next rw_rule1 rw_rule2) *)

(*** Database ***)

let refresh_rewrite_rule_ext rw_ext = 
  { rw_ext with rw = refresh_rewrite_rule rw_ext.rw }

let subsumes_strict_ext database rw_ext_gen rw_ext_ins = 
  (* print_string "**** Strict subsubmes_ext:\n";
  Printf.printf "Gen rule: %s with strict = %b\n" (string_of_rewrite_rule rw_ext_gen.rw) rw_ext_gen.strict;
  Printf.printf "Ins rule: %s with strict = %b\n" (string_of_rewrite_rule rw_ext_ins.rw) rw_ext_ins.strict; *)
  (!extended_subsume || (not rw_ext_gen.strict || rw_ext_ins.strict)) &&
  subsumes_strict database rw_ext_gen.rw rw_ext_ins.rw
  
(* let subsumes_strict_ext database rw_ext_gen rw_ext_ins =
  Statistic.record_notail Statistic.time_subsumes_strict_ext (fun () -> subsumes_strict_ext database rw_ext_gen rw_ext_ins) *)

let display_database database =
  Printf.printf "Constraint system R:\n";
  display_list (fun () -> print_string "  Empty\n") (fun db_entry -> Printf.printf "  %s\n" (string_of_rewrite_rule db_entry.rw_ext.rw)) "" database.rwsys_R;
  Printf.printf "Queue:\n";
  if Rule_queue.is_empty database.queue_R
  then Printf.printf "  Empty\n"
  else Rule_queue.iter database.queue_R (fun rw_ext -> Printf.printf " %s\n" (string_of_rewrite_rule rw_ext.rw))  

let cleanup database =
  if database.rule_inserted mod 200 = 0
  then database.rwsys_R <- List.filter (fun entry -> entry.active) database.rwsys_R

exception Increased_Rn of rewrite_rule list

let rec count_AC_symbol = function
  | Flattened.FVar _ -> 0
  | Flattened.FFunc(_,args) -> List.fold_left (fun c t -> c + count_AC_symbol t) 0 args
  | Flattened.FAC(_,args_m) -> List.fold_left (fun c (t,k) -> c + (k * (count_AC_symbol t)) + k) (-1) args_m

let count_AC_symbol_rw rw = count_AC_symbol rw.lhs.flattened + count_AC_symbol rw.rhs.flattened

let add_rewrite_rule database rw_rule = 
  database.rule_computed <- database.rule_computed + 1;
  (* incr rule_computed; *)
  if database.rule_computed mod 20000 = 0
  then (Printf.printf "Number of rules computed: %d\n" database.rule_computed; flush_all ());

  if !verbose_everyrule
  then 
    begin
      Printf.printf "Rule computed (%d) %s\n" !rule_computed (string_of_rewrite_rule rw_rule);
      flush_all ();
    end;

  if (* Rule EQ and Rule Ord *)
    (!order_strong_computable && Order.compare_strong rw_rule.lhs.flattened rw_rule.rhs.flattened <> Unknown) ||
    (not !order_strong_computable && (
      Flattened.equal rw_rule.lhs.flattened rw_rule.rhs.flattened ||
      Flattened.is_subterm rw_rule.lhs.flattened rw_rule.rhs.flattened
      )
    )
  then ()
  else
    let is_less = !order_strong_computable && Order.compare_strong rw_rule.rhs.flattened rw_rule.lhs.flattened = Less in
    let rw_ext = { rw = rw_rule; strict = is_less } in
    (* Printf.printf "Rule: %s with strict = %b\n" (pretty_string_of_rewrite_rule rw_ext.rw) rw_ext.strict; *)
    if (* We check if the rule is not subsumed by an existing rule *)
      List.exists (fun db_entry -> db_entry.active && subsumes_strict_ext database db_entry.rw_ext rw_ext) database.rwsys_R ||
      Rule_queue.exists database.queue_R (fun q_rw_ext -> subsumes_strict_ext database q_rw_ext rw_ext) 
    then ()
    else
      begin 
        (* We test if the rule needs to be added in Rn *)
        if is_less && not !convergent && !update_Rn
        then 
          begin 
            match simplify_lhs_rw_rule database.rwsysRn rw_rule with
            | None -> ()
            | Some rw_rule' -> 
                if List.exists (fun rw -> subsumes rw rw_rule') database.rwsysRn
                then ()
                else
                  let rwsysRn' = List.filter (fun rw -> not (subsumes rw_rule' rw)) database.rwsysRn in
                  raise (Increased_Rn (rwsysRn' @ [rw_rule']))
          end;

        (* We remove from the database the rules subsumed by rw_rule' *)
        List.iter (fun db_entry -> 
          if db_entry.active && subsumes_strict_ext database rw_ext db_entry.rw_ext
          then db_entry.active <- false
        ) database.rwsys_R;
        Rule_queue.filter database.queue_R (fun q_rw_ext -> not (subsumes_strict_ext database rw_ext q_rw_ext));

        if !verbose_augmented_R
        then 
          begin
            Printf.printf "  Added rewrite rule: %s\n" (string_of_rewrite_rule rw_ext.rw);
            flush_all ()
          end;

        Rule_queue.add database.queue_R rw_ext (count_AC_symbol_rw rw_ext.rw)
      end

let add_rewrite_rule_all database rw_rule =
  if !verbose_everyrule && !rule_computed > 184800
    then 
      begin
        Printf.printf "Normalisation of %s\n" (string_of_rewrite_rule rw_rule);
        flush_all ();
      end;
  normalise (fun rw_rule1 ->
    if !verbose_everyrule && !rule_computed > 184800
      then 
        begin
          Printf.printf "After first Normalisation : %s\n" (string_of_rewrite_rule rw_rule1);
          flush_all ();
        end;
    add_rewrite_rule database rw_rule1;
    normalise (fun rw_rule2 ->
      add_rewrite_rule database rw_rule2
    ) database.rwsysRn (reverse rw_rule1)
  ) database.rwsysRn rw_rule

let add_rewrite_rule_convergent database = 
  normalise (add_rewrite_rule database) database.rwsysRn

let rec generate_extended_signature_one_loop database = match Rule_queue.get database.queue_R with
  | None -> 
      cleanup database;
      List.map (fun entry -> entry.rw_ext.rw) database.rwsys_R
  | Some rw_ext ->
      if !verbose_everyrule
      then 
        begin
          Printf.printf "\n--- Inside loop - before normalisation\n";
          Printf.printf "Selected rewrite rule (sel_rw): %s\n" (string_of_rewrite_rule rw_ext.rw);
          display_database database;
          flush_all ();
        end;
      let add = 
        if !convergent
        then add_rewrite_rule_convergent database
        else add_rewrite_rule_all database
      in

      (* let add rw = 
        Statistic.record_notail Statistic.time_add (fun () -> add rw)
      in *)

      (* We add the rule *)
      let entry = { rw_ext = (refresh_rewrite_rule_ext rw_ext); active = true } in
      database.rwsys_R <- entry :: database.rwsys_R;
      database.rule_inserted <- database.rule_inserted + 1;

      if database.rule_inserted mod 1 = 0
      then (Printf.printf "Number of rules inserted: %d (queue remaining: %d)\n" database.rule_inserted (Rule_queue.length database.queue_R); flush_all ());

      if !verbose_loop
      then 
        begin
          Printf.printf "\n--- Inside loop\n";
          Printf.printf "Selected rewrite rule (sel_rw): %s\n" (string_of_rewrite_rule rw_ext.rw);
          display_database database;
          flush_all ();
        end;

      let rev_rw_ext = reverse rw_ext.rw in

      (* Overlapping En <-> rw_ext *)
      if !verbose_loop
      then (Printf.printf "**Overlapping En <-> sel_rw\n"; flush_all ());

      List.iter (fun rw_rule ->
        if !verbose_everyrule
        then 
          begin
            Printf.printf "Overlap between %s and %s\n" (string_of_rewrite_rule rw_rule) (string_of_rewrite_rule rw_ext.rw);
            flush_all ();
          end;
        overlap_rules add rw_rule rw_ext.rw  
      ) database.rwsysEn;

      if !verbose_loop
      then (Printf.printf "**Overlapping R <-> sel_rw\n"; flush_all ());

      (* Overlapping R <-> rw_ext *)
      List.iter (fun db_entry ->
        if db_entry.active
        then
          begin
            if !verbose_everyrule
            then 
              begin
                Printf.printf "Overlap between %s and %s\n" (string_of_rewrite_rule db_entry.rw_ext.rw) (string_of_rewrite_rule rw_ext.rw);
                flush_all ();
              end;
            overlap_rules add db_entry.rw_ext.rw rw_ext.rw;
            if not !convergent
            then 
              begin 
                let rev_rule = reverse db_entry.rw_ext.rw in
                if !verbose_everyrule
                then 
                  begin
                    Printf.printf "Overlap between %s and %s\n" (string_of_rewrite_rule rev_rule) (string_of_rewrite_rule rw_ext.rw);
                    flush_all ();
                  end;
                overlap_rules add (reverse db_entry.rw_ext.rw) rw_ext.rw
              end
          end
        else ()
      ) database.rwsys_R;

      if !verbose_loop
      then (Printf.printf "**Overlapping sel_rw <-> R\n"; flush_all ());

      (* Overlapping rw_ext <-> R *)
      List.iter (fun db_entry ->
        if db_entry != entry && db_entry.active
        then
          begin
            if !verbose_everyrule
            then 
              begin
                Printf.printf "Overlap between %s and %s\n" (string_of_rewrite_rule rw_ext.rw) (string_of_rewrite_rule db_entry.rw_ext.rw);
                flush_all ();
              end;
            overlap_rules add rw_ext.rw db_entry.rw_ext.rw;
            if not !convergent
            then
              begin
                if !verbose_everyrule
                then 
                  begin
                    Printf.printf "Overlap between %s and %s\n" (string_of_rewrite_rule rev_rw_ext) (string_of_rewrite_rule db_entry.rw_ext.rw);
                    flush_all ();
                  end;
                overlap_rules add rev_rw_ext db_entry.rw_ext.rw
              end
          end
        else ()
      ) database.rwsys_R;

      (* Cleanup of the table *)
      cleanup database;

      generate_extended_signature_one_loop database
        
let initialisation_generate database rwsysRn eqE' =

  database.rwsys_R <- [];
  Rule_queue.clear database.queue_R;
  database.rule_inserted <- 0;
  database.rwsysRn <- rwsysRn;

  let add rw_rule = 
    let rw_rule' = refresh_rewrite_rule rw_rule in
    if !verbose_everyrule
      then 
        begin
          Printf.printf "Normalising rule %s\n" (string_of_rewrite_rule rw_rule');
          flush_all ();
        end;
    if !convergent
    then add_rewrite_rule_convergent database (refresh_rewrite_rule rw_rule)
    else add_rewrite_rule_all database (refresh_rewrite_rule rw_rule)
  in

  List.iter add rwsysRn;
  List.iter add eqE'

let display_rewrite_rule_list l =
  display_list (fun () -> print_string "  Empty\n") (fun rw -> Printf.printf "  %s\n" (string_of_rewrite_rule rw)) "" l

let finalise rwsysR = 
  let conv = 
    Order.order_chosen := ACRPO;
    if List.for_all (fun rw -> Order.compare_strong rw.rhs.flattened rw.lhs.flattened = Less) rwsysR
    then Some rwsysR
    else
      begin 
        Order.order_chosen := CountSymbol;
        if List.for_all (fun rw -> Order.compare_strong rw.rhs.flattened rw.lhs.flattened = Less) rwsysR
        then Some rwsysR
        else None
      end
  in
  let rec generate_fresh_vars = function
    | 0 -> []
    | i -> (Var (fresh_variable ())) :: (generate_fresh_vars (i-1))
  in
  conv,
  List.map (fun f -> 
    let t = Func(f,generate_fresh_vars f.f_arity) in
    let rt = recorded_term_of_term t in
    { lhs = rt; rhs = rt }
  ) !all_symbols
  @ rwsysR


let generate_extended_signature rwsysRn_op eqE' = 

  let to_rewrite_rule s t = 
    { lhs = recorded_term_of_term s; rhs = recorded_term_of_term t }
  in

  Printf.printf "--- Initial maude theory\n";
  Maude_function.print_module stdout;
  flush_all ();

  let rwsysRn = match rwsysRn_op with
    | None -> []
    | Some (l,is_conv) ->
        if is_conv 
        then Printf.printf "Convergent rewrite rules declared\n"
        else Printf.printf "Terminating rewrite rules declared\n";

        convergent := is_conv;

        let rwsysRn = List.map (fun (s,t) -> to_rewrite_rule s t) l in

        if !Order.fixed_order
        then 
          if
            List.for_all (fun rw_rule -> 
            Order.compare_strong rw_rule.rhs.flattened rw_rule.lhs.flattened = Less) rwsysRn
          then 
            begin
              Printf.printf "Chosen reduction order compatible with rewrite system\n";
              order_strong_computable := true;
              rwsysRn
            end
          else 
            begin
              Printf.printf "Chosen reduction order not compatible with rewrite system\n";
              order_strong_computable := false;
              rwsysRn
            end
        else
          begin
            Order.order_chosen := ACRPO;
            let test_ACRPO = List.for_all (fun rw_rule -> Order.compare_strong rw_rule.rhs.flattened rw_rule.lhs.flattened = Less) rwsysRn in
            Order.order_chosen := CountSymbol;
            let test_CountSymbol = List.for_all (fun rw_rule -> Order.compare_strong rw_rule.rhs.flattened rw_rule.lhs.flattened = Less) rwsysRn in
            if test_ACRPO 
            then 
              begin 
                Order.order_chosen := ACRPO;
                order_strong_computable := true;
                Printf.printf "Reduction order (ACRPO) compatible with rewrite system\n";
                rwsysRn
              end
            else if test_CountSymbol 
            then 
              begin 
                Order.order_chosen := CountSymbol;
                order_strong_computable := true;
                Printf.printf "Reduction order (CountSymbol) compatible with rewrite system\n";
                rwsysRn
              end
            else 
              begin
                Order.order_chosen := ACRPO;
                Printf.printf "Reduction orders not compatible with rewrite system\n";
                order_strong_computable := false;
                rwsysRn
              end  
        end    
  in

  if rwsysRn <> [] && !convergent
  then 
    begin 
      if check_convergence rwsysRn
      then Printf.printf "Convergence of the rewrite rules given as input was verified\n"
      else Printf.printf "WARNING: Convergence of the rewrite rules given as input could not be verified. Result could be wrong if the assumption is not correct.\n";
    end;

  (* Generate AC rules *)
  let eqEn = 
    List.fold_left (fun acc f -> match f.f_cat with 
      | Syntactic -> acc
      | _ ->
          let x = Var(fresh_variable ()) in
          let y = Var(fresh_variable ()) in
          let c_rw = (Func(f,[x;y]),Func(f,[y;x])) in

          let x = Var(fresh_variable ()) in
          let y = Var(fresh_variable ()) in
          let z = Var(fresh_variable ()) in
          let a_rw = (Func(f,[Func(f,[x;y]);z]), Func(f,[x;Func(f,[y;z])])) in
        
          c_rw :: a_rw :: acc
    ) [] !all_symbols
  in

  let rwsysEn = 
    let x = Var(fresh_variable ()) in
    let y = Var(fresh_variable ()) in
    let z = Var(fresh_variable ()) in

    List.fold_left (fun acc f -> match f.f_cat with 
      | Syntactic -> acc
      | _ ->
          let c_rw = to_rewrite_rule (Func(f,[x;y])) (Func(f,[y;x])) in
          let a_rw1 = to_rewrite_rule (Func(f,[Func(f,[x;y]);z])) (Func(f,[x;Func(f,[y;z])])) in
          let a_rw2 = to_rewrite_rule (Func(f,[x;Func(f,[y;z])])) (Func(f,[Func(f,[x;y]);z])) in
          (refresh_rewrite_rule c_rw) :: (refresh_rewrite_rule a_rw1) :: (refresh_rewrite_rule a_rw2) :: acc
    ) [] !all_symbols
  in

  let rwsysE' =  
    List.fold_right (fun (s,t) acc -> 
      let rw = to_rewrite_rule s t in
      if !convergent
      then rw::acc
      else  
        let rw' = refresh_rewrite_rule (reverse rw) in
        rw::rw'::acc 
    ) eqE' [] 
  in

  let database = 
    {
      rwsys_R = [];
      queue_R = Rule_queue.new_queue ();
      rule_inserted = 0;
      rule_computed = 0;
      rwsysEn = rwsysEn;
      rwsysRn = rwsysRn
    }
  in

  Printf.printf "\n--- Starting Generate extended signature\n";
  Printf.printf "Rewrite system rwsysEn:\n";
  display_rewrite_rule_list rwsysEn;
  print_string "\n\n";
  flush_all ();

  let rec main_loop rwsysRn =
    if !verbose_loop
    then 
      begin
        Printf.printf "\n--- Main loop with new Rn\n";
        Printf.printf "Rewrite system Rn:\n";
        display_rewrite_rule_list rwsysRn;
        flush_all ();
      end;
    try 
      initialisation_generate database rwsysRn rwsysE';
      let rwsysR = generate_extended_signature_one_loop database in
      let conv_op,final_R = finalise rwsysR in
      (final_R,rwsysRn,eqEn), conv_op, database.rule_computed
    with 
      | Increased_Rn rwsysRn' -> main_loop rwsysRn'
  in

  main_loop rwsysRn


(* let generate_extended_signature rwsysRn_op eqE' = 
  Statistic.record_notail Statistic.time_generate_extended_signature (fun () -> generate_extended_signature rwsysRn_op eqE') *)