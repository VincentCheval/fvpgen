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
open Utils
open Flattened

let count_subst = ref 1


let time_old = ref 0.0
let time_new = ref 0.0

let record f_old f_new = 
  (* Old *)
  let t = Unix.times() in
  let start_time = (t.tms_utime +. t.tms_stime) in
  let r1 = f_old () in
  let t = Unix.times() in
  let end_time = (t.tms_utime +. t.tms_stime) in
  time_old := end_time -. start_time +. !time_old;

  (* New *)
  let t = Unix.times() in
  let start_time = (t.tms_utime +. t.tms_stime) in
  let r2 = f_new () in
  let t = Unix.times() in
  let end_time = (t.tms_utime +. t.tms_stime) in
  time_new := end_time -. start_time +. !time_new;

  r1,r2

let count_unify = ref 0

module Unify = 
struct
  
  open Flattened

  module ElementaryNew = 
  struct

    open Flattened

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

    let display_vector_nonewline f_print m = 
      for i = 0 to Array.length m - 1 do 
        Printf.printf "%s  " (f_print m.(i))
      done
      
    (* DFS Hullot Tree *)

    type status =
      | NotVisited
      | Visited
      | Finished

    type vertex = 
      {
        mutable status : status;
        successors : (int (* Index *) * int (** Bit representation *)) list
      }

    type occurence_data = 
      {
        vertex_tbl: vertex Array.t;
        roots: int (** Index *) list
      }

    let display_occurrence_data nb_solutions occur_data = 
      Printf.printf "*** Occurrrence data:\n";
      Printf.printf "Roots: %s\n" (string_of_list string_of_int "; " occur_data.roots);
      Printf.printf "Vertex_tbl:\n";
      Array.iteri (fun i vertex ->
        Printf.printf "  %d -> %s\n" i (string_of_list (fun (j,bit_trans) -> Printf.sprintf "(%d,%s)" j (int2bin nb_solutions bit_trans)) " -- " vertex.successors) 
      ) occur_data.vertex_tbl

    exception FoundCycle

    let check_no_cycle n occur_data subset_bits =

      let rec dfs idx = 
        let vertex = occur_data.vertex_tbl.(idx) in
        match vertex.status with 
        | Finished -> ()
        | Visited -> raise FoundCycle
        | NotVisited ->
            vertex.status <- Visited;
            List.iter (fun (idx,repr_bits) ->
              if subset_bits land repr_bits <> 0
              then dfs idx
            ) vertex.successors;
            vertex.status <- Finished
      in

      try 
        List.iter dfs occur_data.roots;
        List.iter (fun idx -> occur_data.vertex_tbl.(idx).status <- NotVisited) occur_data.roots;
        true
      with FoundCycle -> 
        List.iter (fun idx -> occur_data.vertex_tbl.(idx).status <- NotVisited) occur_data.roots;
        false

    let dfs_hullot_tree f_next n all_bits constants_bits occur_data =
      let init_full_one = -1 lsr (Sys.int_size - n) in
    
      let big_enough subset_bits = List.for_all (fun vi -> subset_bits land vi <> 0) all_bits
      in
      let small_enough subset_bits = 
        List.for_all (fun vi -> (subset_bits land vi) land ((subset_bits land vi) -1) = 0) constants_bits &&
        check_no_cycle n occur_data subset_bits
      in
      
      (* When [sign_greater = true], it corresponds to >. *)
      let rec dfs next_dfs pre a k sign_greater = 
        (* Printf.printf "Dfs pre = %s, a = %s, k = %d, sign_greater = %b\n" (int2bin n pre) (int2bin n a) k sign_greater; *)
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
          nb_variables: int;  (** Number of variables in the initial problem *)
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
    
      let display_t store = 
        Array.iteri (fun i elt ->
          if i = Array.length store.elts - 1
          then 
            begin 
              Printf.printf "- Variables :\n";
              List.iter (fun sol ->
                display_vector string_of_int sol;
              ) elt
            end
          else
            begin 
              Printf.printf "- Constant %d:\n" i;
              List.iter (fun sol -> display_vector string_of_int sol) elt
            end
        ) store.elts
        
      let display_t_frozen store = 
        Array.iteri (fun i elt ->
          if i = Array.length store.elts_f - 1
          then 
            begin 
              Printf.printf "- Variables :\n";
              List.iter (fun (sol,defect) ->
                print_string "Sol ";
                display_vector_nonewline (fun (k,b) -> Printf.sprintf "(%d,%b)" k b) sol;
                print_string " with defect ";
                display_vector string_of_int defect;
              ) elt
            end
          else
            begin 
              Printf.printf "- Constant %d:\n" i;
              List.iter (fun (sol,defect) ->
                print_string "Sol ";
                display_vector_nonewline (fun (k,b) -> Printf.sprintf "(%d,%b)" k b) sol;
                print_string " with defect ";
                display_vector string_of_int defect;
              ) elt
            end
        ) store.elts_f
        
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
    
      (* Add the content of store2 in store1 *)
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
          for j = 0 to Array.length storage.elts_t.(i) - 1 do 
            let p' = !p lsl 1 in
            p := if storage.elts_t.(i).(j).(idx) <> 0 then succ p' else p'
          done
        done;
        !p
    
      let generate_bitvector_of_all_constants ground_constants storage =
        let rec loop nb_remaing_solutions idx =
          if idx = storage.nb_constants
          then []
          else
            if ground_constants.(idx) = None
            then
              let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
              let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in
              ((-1 lsr (Sys.int_size - nb_solution_of_constant_idx)) lsl nb_remaing_solutions) :: loop nb_remaing_solutions (idx+1)
            else 
              begin
                (* Printf.printf "Loop nb_remaing_solutions = %d, idx = %d\n" nb_remaing_solutions idx; *)
                let p = ref 0 in
                for i = 0 to storage.nb_constants - 1 do
                  for j = 0 to Array.length storage.elts_t.(i) - 1 do 
                    let p' = !p lsl 1 in
                    p := if storage.elts_t.(i).(j).(idx) <> 0 then succ p' else p'
                  done
                done;
                let full_p = !p lsl Array.length storage.elts_t.(storage.nb_constants) in
                
                let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
                let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in

                (* Printf.printf "Value p: %s, nb_sol_const_idx: %d, nb_remainig: %d, p_pure_idx: %s, p_full: %s\n" 
                  (int2bin storage.nb_elts_t !p) nb_solution_of_constant_idx nb_remaing_solutions
                  (int2bin storage.nb_elts_t p_pure_idx) (int2bin storage.nb_elts_t full_p)
                  ; *)

                full_p :: loop nb_remaing_solutions (idx+1)
              end
        in
        loop storage.nb_elts_t 0
    
      let generate_bitvectors ground_constants storage = 
        let constant_bitvectors = generate_bitvector_of_all_constants ground_constants storage in
        let all_bitvectors = ref constant_bitvectors in
        for idx = storage.nb_constants to storage.nb_constants + storage.nb_variables - 1 do
          all_bitvectors := generate_bitvectors_of_variable storage idx :: !all_bitvectors
        done;
        constant_bitvectors, !all_bitvectors
    
      (** Generation of the occurrence data *)

      let generate_occurrence_data (occur_variables:(int list *int) Array.t) storage =

        let vertex_tbl = Array.make storage.nb_variables { status = NotVisited; successors = [] } in

        let build_transition_bit idx_xi bit_xj =
          (* if !count_unify = 1
            then 
              begin
                Printf.printf "build_transition_bit (%d,%s)\n" idx_xi (int2bin storage.nb_variables bit_xj);
                flush_all ();
              end; *)
          let p = ref 0 in
          for i = 0 to storage.nb_constants - 1 do
            for j = 0 to Array.length storage.elts_t.(i) - 1 do 
              let p' = !p lsl 1 in
              if storage.elts_t.(i).(j).(idx_xi+storage.nb_constants) <> 0 && bit_xj land (snd occur_variables.(i)) <> 0
              then p := succ p'
              else p := p'
            done
          done;
          !p lsl (Array.length storage.elts_t.(storage.nb_constants))
        in

        let roots = ref [] in

        for i = 0 to storage.nb_variables - 1 do
          let bit_xj = ref (1 lsl (storage.nb_variables - 1)) in
          let succ = ref [] in
          for j = 0 to storage.nb_variables - 1 do
            if i <> j 
            then 
              begin
                let transition_bit = build_transition_bit i !bit_xj in
                if transition_bit <> 0
                then succ := (j,transition_bit) :: !succ
              end;
            bit_xj := !bit_xj lsr 1
          done;
          vertex_tbl.(i) <- { status = NotVisited; successors = !succ };
          if !succ <> [] then roots := i :: !roots
        done;

        { vertex_tbl = vertex_tbl; roots = !roots }

      (** Suitable_bitsubset_to_substitutions *)
      let suitable_bitsubset_to_substitution storage f_AC constants variables ground_constants p = 
        
        (* Reset the recorded term in ground_constants *)
        Array.iter (function None -> () | Some ref_t -> ref_t := dummy) ground_constants;

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
                Array.iteri (fun j ground -> match ground with
                  | None -> ()
                  | Some ref_t ->
                      let k = sol.(j) in
                      if k <> 0
                        then 
                          begin
                            if k <> 1 || !ref_t != dummy then failwith "[Elementary.Storage_solutions] The 'smaller than' test should have discarded this case"; 
                            ref_t := storage.associated_variables.(i)
                          end
                ) ground_constants;
                loop_vars (i - 1) (bit_i lsl 1)
              end
        in

        let rec loop_constants i ith_constant constant sols_constant bit_i =
          (* if !count_unify = 1
          then Printf.printf "loop_constants(%d,%d,%s,%s)\n" i ith_constant (Flattened.string_of_term constant) (int2bin storage.nb_elts_t bit_i); *)
          if i = -1
          then bit_i
          else
            if bit_i land p = 0 (* The subset do not contain the solution *)
            then loop_constants (i - 1) ith_constant constant sols_constant (bit_i lsl 1)
            else 
              begin 
                let sol = sols_constant.(i) in
                (* if !count_unify = 1
                then
                  begin 
                    Printf.printf "Sol: ";
                    display_vector string_of_int sol
                  end; *)

                for j = 0 to Array.length term_links -1 do
                  let k = sol.(j+storage.nb_constants) in
                  if k <> 0
                  then term_links.(j) <- (constant,k) :: term_links.(j)
                done;
                Array.iteri (fun j ground -> match ground with
                  | None -> ()
                  | Some ref_t ->
                    if j != ith_constant
                    then 
                      let k = sol.(j) in
                      if k <> 0
                      then 
                        begin
                          (* if !count_unify = 1
                          then
                            begin 
                              Printf.printf "Recording a term with j: %d\n" j
                            end; *)
                          if k <> 1 || !ref_t != dummy then failwith "[Elementary.Storage_solutions] The 'smaller than' test should have discarded this case"; 
                          ref_t := constant
                        end
                ) ground_constants;
                (bit_i lsl (i + 1))
              end
        in
    
        let rec loop_all_constants ith_constant bit_i = 
          (* Printf.printf "loop_all_constants(%d,%s)\n" ith_constant (int2bin storage.nb_elts_t bit_i); *)
          if ith_constant = - 1
          then ()
          else
            let sols_constant = storage.elts_t.(ith_constant) in
            let bit_i' = loop_constants (Array.length sols_constant - 1) ith_constant constants.(ith_constant) sols_constant bit_i in
            loop_all_constants (ith_constant-1) bit_i'
        in
    
        let bit_i = loop_vars (Array.length storage.associated_variables - 1) 1 in
        loop_all_constants (storage.nb_constants - 1) bit_i;
    
        for i = 0 to Array.length variables - 1 do
          match term_links.(i) with
            | [] -> failwith "[suitable_bitsubset_to_substitution] There should be a term to link."
            (* | [FVar ({v_link = NoLink; } as v),1] -> link v (FTLink (FVar variables.(i))) *)
            | [t,1] -> link variables.(i) (FTLink t)
            | mt -> link variables.(i) (FTLink (FAC(f_AC,mt)))
        done
    end
    
    (* In [solve_system_diophantine_equations nb_constants matrix_system], we assume that
      then first [nb_constants] columns of [matrix_system] represents constants. *)
    let solve_system_diophantine_equations nb_constants (occur_variables:(int list * int) Array.t) ground_constants matrix_system =
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
        (* if !count_unify = 1
          then 
            begin
              Printf.printf "*** set_Vk_not_in_Mk:\n";
              Storage_solutions.display_t_frozen set_Vk_not_in_Mk;
              Printf.printf "*** set_Vk_in_Mk:\n";
              Storage_solutions.display_t set_Vk_in_Mk;
              Printf.printf "*** set_rest_Mk:\n";
              Storage_solutions.display_t set_rest_Mk;
              print_string "-------\n"
            end; *)

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
                          (* Froze the previous successful index. *)
                          List.iter (fun l ->
                            new_v.(l) <- (fst new_v.(l), true);
                          ) !success_j;

                          (* If j was a non-ground constant, froze the variables that occur in the constant *)
                          if j < nb_constants && ground_constants.(j) <> None
                          then 
                            begin 
                              if fst new_v.(j) <> 1 then failwith "It should be one";
                              new_v.(j) <- (1, true);
                              List.iter (fun k -> new_v.(k) <- (fst new_v.(k), true)) (fst occur_variables.(j))
                            end;

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
      
      (* Initialise the sets *)
      let e_frozen_template = Array.make nb_variables (0,false) in

      (* Froze all the ground ground constants *)
      for j = 0 to nb_constants - 1 do
        if ground_constants.(j) = None
        then e_frozen_template.(j) <- (0,true)
      done;

      let e_frozen_template_ground = Array.copy e_frozen_template in

      for j = 0 to nb_constants - 1 do 
        if is_null initial_defects.(j)
        then 
          let ej = Array.make nb_variables 0 in
          ej.(j) <- 1;
          Storage_solutions.add init_set_Vk_in_Mk (min j nb_constants) ej;
          if ground_constants.(j) = None
          then
            begin
              e_frozen_template.(j) <- (0,true);
              e_frozen_template_ground.(j) <- (0,true)
            end
          else e_frozen_template.(j) <- (0,true)
        else
          begin
            let ej = 
              if ground_constants.(j) = None
              then 
                begin 
                  let ej' = Array.copy e_frozen_template_ground in
                  e_frozen_template.(j) <- (0,true);
                  e_frozen_template_ground.(j) <- (0,true);
                  ej'
                end
              else
                begin 
                  let ej' = Array.copy e_frozen_template in
                  e_frozen_template.(j) <- (0,true);
                  ej'
                end
            in
            ej.(j) <- (1,true);
            (* Froze the variables that occur in the constant *)
            List.iter (fun k -> ej.(k+nb_constants) <- (0,true)) (fst occur_variables.(j));

            Storage_solutions.add_frozen init_set_Vk_not_in_Mk (min j nb_constants) (ej,initial_defects.(j));
          end
      done;
      
      for j = nb_constants to nb_variables - 1 do 
        if is_null initial_defects.(j)
        then 
          let ej = Array.make nb_variables 0 in
          ej.(j) <- 1;
          Storage_solutions.add init_set_Vk_in_Mk (min j nb_constants) ej
        else
          begin
            let ej = Array.copy e_frozen_template in
            ej.(j) <- (1,false);

            Storage_solutions.add_frozen init_set_Vk_not_in_Mk (min j nb_constants) (ej,initial_defects.(j));
          end;
        e_frozen_template.(j) <- (0,true);
      done;
    
      build_M init_set_Vk_not_in_Mk init_set_Vk_in_Mk;
    
      set_rest_Mk
    
    module MatrixGeneration = struct
    
      let dummy_vars = fresh_variable ()
    
      (* Should be improved when the terms will be DAG *)
      type t = 
        {
          mutable vars: (variable * int Array.t) list;
          mutable nb_vars: int;
          mutable constants: (term * bool (* Is ground when true *) * (int list * int) (* Occur variables *) * int Array.t (* Coeffs *)) list;
          mutable nb_constants: int;
          nb_equations: int
        }
    
      (* let create_from_matching (vars_mt,const_mt) =
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
    *)
      let create nb_equations = 
        {
          vars = [];
          nb_vars = 0;
          constants = [];
          nb_constants = 0;
          nb_equations = nb_equations
        }
    
      let add_variable store ith_eq v k = 
        let rec loop list_variables = match list_variables with
          | [] -> 
              (* The variable is greater than all *)
              let coeffs = Array.make store.nb_equations 0 in
              coeffs.(ith_eq) <- k;
              store.nb_vars <- store.nb_vars + 1;
              [v,coeffs]
          | ((v',coeffs') as v_coeff)::q_vars ->
              match compare_variable v v' with
              | 0 -> 
                  coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
                  list_variables
              | -1 -> 
                  (* The variable was not recorded *)
                  let coeffs = Array.make store.nb_equations 0 in
                  coeffs.(ith_eq) <- k;
                  store.nb_vars <- store.nb_vars + 1;
                  (v,coeffs) :: list_variables
              | _ -> v_coeff :: loop q_vars
        in
        store.vars <- loop store.vars
    
      let add_constant store t is_ground occur_vars ith_eq k = 
        let rec loop list_constants = match list_constants with
          | [] -> 
              (* The constant is greater than all *)
              let coeffs = Array.make store.nb_equations 0 in
              coeffs.(ith_eq) <- k;
              store.nb_constants <- store.nb_constants + 1;
              [t,is_ground,occur_vars,coeffs]
          | ((t',_,_,coeffs') as t_coeff)::q_const ->
              match compare t t' with
              | 0 -> 
                  coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
                  list_constants
              | -1 -> 
                  (* The variable was not recorded *)
                  let coeffs = Array.make store.nb_equations 0 in
                  coeffs.(ith_eq) <- k;
                  store.nb_constants <- store.nb_constants + 1;
                  (t,is_ground,occur_vars,coeffs) :: list_constants
              | _ -> t_coeff :: loop q_const
        in
        store.constants <- loop store.constants
    
      type link+= ILink of int

      let filter_index_bool bool_ar = 
        let p = ref 0 in
        let rec loop acc i_repr = function
          | -1 -> acc, !p
          | i -> 
              if bool_ar.(i)
              then 
                begin 
                  p := !p lor i_repr; 
                  loop (i::acc) (i_repr lsl 1) (i-1)
                end
              else loop acc (i_repr lsl 1) (i-1)
        in
        loop [] 1 (Array.length bool_ar - 1)

      let unfold_term_with_occur_vars nb_variables t =
        let ground = ref true in
        let occur_variables = Array.make nb_variables false in

        let rec loop t = match t with
          | FVar { v_link = FTLink t; _ } -> loop t
          | FVar { v_link = ILink j; _ } ->
              occur_variables.(j) <- true;
              ground := false;
              t
          | FVar _ -> ground := false; t
          | FFunc(f,args) -> 
              let args' = List.mapq loop args in
              if args == args' then t else FFunc(f,args')
          | FAC(f,margs) -> 
              let margs' = 
                List.mapq (fun ((t,k) as pair)-> 
                  let t' = loop t in
                  if t == t' then pair else (t',k)
                ) margs
              in
              if margs' == margs then t else FAC(f,margs') 
        in

        let t_unfolded = loop t in
        !ground, filter_index_bool occur_variables, t_unfolded


      let from_unification_equations f_AC system_equations = 
        if system_equations = []
        then failwith "[Flattened.Elementary.MatrixGeneration.from_matching_equations] The system of equations should not be empty";

        let nb_equations = List.length system_equations in
        let store = create nb_equations in

        (* Unfold variables and F_AC *)
        let system_equations = 
          List.map (fun (left_l,right_l) ->
            let new_left_l = ref [] in
            let new_right_l = ref [] in 
            List.iter (unfold_AC_only f_AC new_left_l) left_l;
            List.iter (unfold_AC_only f_AC new_right_l) right_l;
            !new_left_l,!new_right_l
          ) system_equations
        in

        let non_variable_terms = ref [] in

        (* Add only variables *)
        List.iteri (fun i (left_eq,right_eq) ->
          List.iter (function (t,k) -> match t with
            | FVar v -> add_variable store i v k
            | t -> non_variable_terms := (i,t,k) :: !non_variable_terms
          ) left_eq;
          List.iter (function (t,k) -> match t with
            | FVar v -> add_variable store i v (-k)
            | t -> non_variable_terms := (i,t,-k) :: !non_variable_terms
          ) right_eq;
        ) system_equations;

        auto_cleanup_no_catch (fun () ->
          (* Link the variables *)
          List.iteri (fun i (v,_) -> link v (ILink i)) store.vars;

          let nb_variables = store.nb_vars in
            
          (* Add terms *)
          List.iter (fun (ith_eq,t,k) ->
            let (is_ground,occur_vars,t_unfolded) = unfold_term_with_occur_vars nb_variables t in
            add_constant store t_unfolded is_ground occur_vars ith_eq k
          ) !non_variable_terms
        );

        let matrix = Array.make_matrix store.nb_equations (store.nb_constants + store.nb_vars) 0 in
        let variables = Array.make store.nb_vars dummy_vars in
        let constants = Array.make store.nb_constants dummy in
        let occur_variables = Array.make store.nb_constants ([],0) in
        let ground_constants = Array.make store.nb_constants None in

        (* Register the variables *)
        List.iteri (fun j (v,coeffs) ->
          variables.(j) <- v;
          Array.iteri (fun i k ->
            matrix.(i).(store.nb_constants+j) <- k
          ) coeffs  
        ) store.vars;

        (* Register the constants *)
        List.iteri (fun j (t,is_ground,occur_vars,coeffs) ->
          constants.(j) <- t;
          occur_variables.(j) <- occur_vars;
          if not is_ground then ground_constants.(j) <- Some (ref dummy);
          Array.iteri (fun i k ->
            matrix.(i).(j) <- k
          ) coeffs  
        ) store.constants;

        (matrix,variables,store.nb_vars,constants,store.nb_constants,occur_variables,ground_constants)


      (* let from_matching_equations system_equations = 
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

            let matrix = Array.make_matrix store.nb_equations (store.nb_constants + store.nb_vars) 0 in
            let variables = Array.make store.nb_vars dummy_vars in
            let constants = Array.make store.nb_constants dummy in
            let occur_variables = Array.make store.nb_constants [] in

            (* Register the variables *)
            List.iteri (fun j (v,coeffs) ->
              variables.(j) <- v;
              List.iteri (fun i k ->
                matrix.(i).(store.nb_constants+j) <- k
              ) coeffs  
            ) store.vars;

            (* Register the constants *)
            List.iteri (fun j (t,coeffs) ->
              constants.(j) <- t;
              List.iteri (fun i k ->
                matrix.(i).(j) <- k
              ) coeffs  
            ) store.constants;
    
            (matrix,variables,store.nb_vars,constants,store.nb_constants,occur_variables)
    *)
    end 
    
    let solve f_next f_AC matrix_system variables nb_variables constants nb_constants occur_variables ground_constants =
      if !count_unify = 1
      then 
        begin 
          print_string "Matrix =\n";
          display_matrix string_of_int matrix_system;
          Printf.printf "Variables (%d) = " nb_variables;
          display_vector string_of_variable variables;
          Printf.printf "Constants (%d) = " nb_constants;
          display_vector string_of_term constants;
          Printf.printf "Occur_variables = ";
          display_vector (fun (l,bit) -> Printf.sprintf "([%s],%s)" (string_of_list string_of_int ";" l) (int2bin nb_variables bit)) occur_variables;
          Printf.printf "Ground constants = ";
          display_vector (function None -> "true" | _ -> "false") ground_constants;
          flush_all ();
        end;
      
      (* Solving the matrix system *)
      let solutions = solve_system_diophantine_equations nb_constants occur_variables ground_constants matrix_system in
      let nb_solutions = solutions.Storage_solutions.nb_elts in
      
      if nb_solutions > Sys.int_size - 2
      then failwith "Limit on the number of solutions reached";
    
      if nb_solutions = 0 then raise NoMatch;
    
      let finalized_solutions = Storage_solutions.finalize nb_constants nb_variables solutions in
    
      if !count_unify = 1
      then 
        begin 
          Printf.printf "\n** Finalized solution\n";
          Storage_solutions.display finalized_solutions;
          flush_all ();
        end;
    
      (* Bit presentation to subset of solutions *)
      let (constant_bitvectors,all_bitvectors) = Storage_solutions.generate_bitvectors ground_constants finalized_solutions in

      if !count_unify = 1
      then 
        begin 
          Printf.printf "\n** Constant bitvectors\n";
          List.iter (fun p ->
            Printf.printf "bit = %s\n" (int2bin nb_solutions p)
          ) constant_bitvectors;
          Printf.printf "\n** All bitvectors\n";
          List.iter (fun p ->
            Printf.printf "bit = %s\n" (int2bin nb_solutions p)
          ) all_bitvectors;
          flush_all ();
        end;

      let occurence_data = Storage_solutions.generate_occurrence_data occur_variables finalized_solutions in
      
      if !count_unify = 1
      then display_occurrence_data finalized_solutions.nb_elts_t occurence_data;

      dfs_hullot_tree (fun f_next_dfs p ->
        try 
          auto_cleanup_noreset (fun () ->
            if !count_unify = 1
            then 
              begin
                Printf.printf "Building the substitution %d with %s\n\n\n" !count_subst (int2bin nb_solutions p);
                flush_all ()
              end;
            Storage_solutions.suitable_bitsubset_to_substitution finalized_solutions f_AC constants variables ground_constants p;
            f_next ()
          )
        with NoMatch -> f_next_dfs ()
      ) nb_solutions all_bitvectors constant_bitvectors occurence_data
    
    (* (** [system_equations] is a list of pairs of multiplicty list. The left hand side are only
        variables and on the right hand side, they are considered as constant. *)
    let matching f_next f_AC system_equations = 
      if system_equations = [] then failwith "[Elementary.matching] The system of equations should not be empty.";
      let (matrix_system,variables,nb_variables,constants,nb_constants,occur_variables) = MatrixGeneration.from_matching_equations system_equations in
    
      solve f_next f_AC matrix_system variables nb_variables constants nb_constants occur_variables []
    *)

    let unification f_next f_AC system_equations = 
      let (matrix_system,variables,nb_variables,constants,nb_constants,occur_variables,ground_constants) = MatrixGeneration.from_unification_equations f_AC system_equations in
      (* Printf.printf "After matrix generation\n";
      flush_all (); *)
      solve (fun () ->
        let new_equations = ref [] in

        for i = 0 to nb_constants - 1 do
          match ground_constants.(i) with
          | None -> ()
          | Some ref_t ->
              if !ref_t != dummy then new_equations := (constants.(i),!ref_t) :: !new_equations
        done;

        f_next !new_equations
      ) f_AC matrix_system variables nb_variables constants nb_constants occur_variables ground_constants;
      
  end

  let rec occurs_check x = function
    | FVar { v_link = FTLink t; _} -> occurs_check x t
    | FVar y -> if x == y then raise NoMatch
    | FFunc(_,args) -> List.iter (occurs_check x) args
    | FAC(_,margs) -> List.iter (fun (t,_) -> occurs_check x t) margs 

  let rec unify_term_aux remaining_problems t1 t2 = match t1, t2 with 
    | FVar v1, FVar v2 when v1 == v2 -> ()
    | FVar { v_link = FTLink t; _}, t' 
    | t', FVar { v_link = FTLink t; _} -> unify_term_aux remaining_problems t t'
    | FVar v1, FVar v2 -> link v1 (FTLink t2)
    | FVar v, t 
    | t, FVar v -> 
        occurs_check v t;
        link v (FTLink t)
    | FFunc(f1,args1), FFunc(f2,args2) -> 
        if f1 != f2 then raise NoMatch;
        List.iter2 (unify_term_aux remaining_problems) args1 args2
    | FAC(f1,margs1), FAC(f2,margs2) ->
        if f1 != f2 then raise NoMatch;
        remaining_problems :=  (f1,margs1,margs2)::!remaining_problems
    | _ -> raise NoMatch

  let unify_term f_next remaining_problems t1 t2 = 
    auto_cleanup_noreset (fun () ->
      let remain_ref = ref remaining_problems in
      unify_term_aux remain_ref t1 t2;
      f_next !remain_ref  
    )

  let rec flatten_term f mlist t k = match t with
    | FVar { v_link = FTLink ((FVar _) as t') } -> flatten_term f mlist t' k
    | FVar { v_link = FTLink (FAC(f',margs')); _ } when f == f' ->
        List.fold_left (fun acc_mlist (t',k') ->
          flatten_term f acc_mlist t' (k*k')
        ) mlist margs'
    | FVar { v_link = FTLink t'; _ } -> add_multiplicity f t' k mlist
    | FAC(f',margs') when f == f' -> 
        List.fold_left (fun acc_mlist (t',k') ->
          flatten_term f acc_mlist t' (k*k')
        ) mlist margs'
    | _ -> add_multiplicity f t k mlist

  let flatten_mterm_list f mlist = 
    List.fold_left (fun acc_mlist (t,k) ->
      flatten_term f acc_mlist t k
    ) [] mlist

  let rec partition_remaining_problems f_target = function
    | [] -> [], []
    | (f,mlist1,mlist2) :: q when f == f_target ->
        let same_f_problems, other_problems = partition_remaining_problems f_target q in
        (flatten_mterm_list f_target mlist1,flatten_mterm_list f_target mlist2)::same_f_problems, other_problems
    | pbl::q -> 
        let same_f_problems, other_problems = partition_remaining_problems f_target q in
        same_f_problems, pbl::other_problems

  let rec solve_remaining_problems f_next remaining_problems = match remaining_problems with
    | [] -> f_next ()
    | (f,_,_) :: _ ->
        let same_f_problems, other_problems = partition_remaining_problems f remaining_problems in
        if same_f_problems = [] then failwith "[Unify.solve_remaining_problems] There should be at least one problem corresponding to the function symbol.";
        ElementaryNew.unification (fun new_equations ->
          if !count_unify = 1
          then 
            begin
              Printf.printf "After ElementaryNew.unification \n";
              let subst = 
                List.fold_left (fun acc v -> match v.v_link with 
                  | FTLink t -> (v,Flattened.copy_term_rec t)::acc
                  | NoLink -> acc
                  | _ -> failwith "[matching_one] Unexpected case"
                ) [] !current_bound_vars
              in
              Printf.printf "Current subst = %s\n" (string_of_subst subst);
              Printf.printf "New equations : %s\n" (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " new_equations);
              flush_all ();
            end;
          auto_cleanup_noreset (fun () ->
            let remain_ref = ref other_problems in
            List.iter (fun (t1,t2) -> unify_term_aux remain_ref t1 t2) new_equations;
            solve_remaining_problems f_next !remain_ref  
          )
        ) f same_f_problems

  let unify f_next eq_list = 
    incr count_unify;
    if !count_unify = 1
      then 
        begin
          Printf.printf "Unification %d of %s\n"
            !count_unify 
            (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
          flush_all ();
        end;
    let vars = get_variables_in_equations eq_list in
    auto_cleanup (fun () ->
      let remain_ref = ref [] in
      List.iter (fun (t1,t2) ->
        unify_term_aux remain_ref t1 t2
      ) eq_list;
      solve_remaining_problems (fun () ->
        let subst = 
          List.fold_left (fun acc v -> match v.v_link with 
            | FTLink t -> (v,Flattened.copy_term_rec t)::acc
            | NoLink -> acc
            | _ -> failwith "[matching_one] Unexpected case"
          ) [] vars
        in
        f_next subst
      ) !remain_ref
    )

  let verify_unifier eq_list subst =
    if not (List.for_all (fun (t1,t2) ->
        let t1' = apply_subst subst t1 in
        let t2' = apply_subst subst t2 in
        equal t1' t2'
      ) eq_list)
    then
      begin
        begin 
          Printf.printf "*** Problem %d: Found a wrong unifier %s\n"
            !count_unify
              (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
          Printf.printf "- Subst = %s\n" (string_of_subst subst);
          failwith "Error"
        end
      end

  (* Does there exists \theta such that x subst2 =AC x subst1\theta for all variables x of the problems *)
  let subst_implies vars subst1 subst2 =
    let list1 = List.map (fun v -> apply_subst subst1 (FVar v)) vars in
    let list2 = List.map (fun v -> apply_subst subst2 (FVar v)) vars in

    find_matching_term_list list1 list2

  let is_subst_implies vars subst1 subst2 =
    let list1 = List.map (fun v -> apply_subst subst1 (FVar v)) vars in
    let list2 = List.map (fun v -> apply_subst subst2 (FVar v)) vars in

    None <> find_matching_term_list list1 list2

  let verify_minimality str eq_list subst_list =
    let header_printed = ref false in
    let vars = get_variables_in_equations eq_list in

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
        Printf.printf "*** Unification %d (%s) not minimal in %s\n"
          !count_unify str
          (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
        Printf.printf "  Number of substitutions in original set: %d\n" set_size;
        Printf.printf "  Number of substitutions in minimal set: %d\n" minimal_set_size;
        Printf.printf "  Gain: %d\n" (set_size - minimal_set_size)
      end
    
  let verify_correctness eq_list subst_maude_l subst_native_l = 
    let vars = get_variables_in_equations eq_list in
    let header_printed = ref false in
    let correct = ref true in

    let display (i2,subst2) =
      if not !header_printed
        then 
          begin 
            header_printed := true;
            Printf.printf "*** Unification %d incorrect in %s\n"
              !count_unify 
              (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
          end;
        Printf.printf "- Subst_%d = %s\n" i2 (string_of_subst subst2)
    in

    let rec loop i = function 
      | [] -> ()
      | subst :: q_subst ->
          if 
            List.for_all (fun subst_native ->
              match subst_implies vars subst_native subst with 
              | None -> true
              | _ -> false
            ) subst_native_l
          then 
            begin 
              display (i,subst);
              correct := false
            end;
          loop (i+1) q_subst
    in

    loop 1 subst_maude_l;
    !correct

end
  
module UnifyMinimal = 
struct
  
  open Flattened

  let rec occurs_check x = function
    | FVar { v_link = FTLink t; _} -> occurs_check x t
    | FVar y -> if x == y then raise NoMatch
    | FFunc(_,args) -> List.iter (occurs_check x) args
    | FAC(_,margs) -> List.iter (fun (t,_) -> occurs_check x t) margs 

  let rec unify_term_aux remaining_problems t1 t2 = match t1, t2 with 
    | FVar v1, FVar v2 when v1 == v2 -> ()
    | FVar { v_link = FTLink t; _}, t' 
    | t', FVar { v_link = FTLink t; _} -> unify_term_aux remaining_problems t t'
    | FVar v1, FVar v2 -> link v1 (FTLink t2)
    | FVar v, t 
    | t, FVar v -> 
        occurs_check v t;
        link v (FTLink t)
    | FFunc(f1,args1), FFunc(f2,args2) -> 
        if f1 != f2 then raise NoMatch;
        List.iter2 (unify_term_aux remaining_problems) args1 args2
    | FAC(f1,margs1), FAC(f2,margs2) ->
        if f1 != f2 then raise NoMatch;
        remaining_problems :=  (f1,margs1,margs2)::!remaining_problems
    | _ -> raise NoMatch

  let rec unify_term_aux_split f_AC same_remaining_problems remaining_problems t1 t2 = match t1, t2 with 
    | FVar v1, FVar v2 when v1 == v2 -> ()
    | FVar { v_link = FTLink t; _}, t' 
    | t', FVar { v_link = FTLink t; _} -> unify_term_aux_split f_AC same_remaining_problems remaining_problems t t'
    | FVar v1, FVar v2 -> link v1 (FTLink t2)
    | FVar v, t 
    | t, FVar v -> 
        occurs_check v t;
        link v (FTLink t)
    | FFunc(f1,args1), FFunc(f2,args2) -> 
        if f1 != f2 then raise NoMatch;
        List.iter2 (unify_term_aux_split f_AC same_remaining_problems remaining_problems) args1 args2
    | FAC(f1,margs1), FAC(f2,margs2) ->
        if f1 != f2 then raise NoMatch;
        if f1 == f_AC
        then same_remaining_problems := (margs1,margs2) :: !same_remaining_problems
        else remaining_problems :=  (f1,margs1,margs2) :: !remaining_problems
    | _ -> raise NoMatch

  module Constraints =
  struct

    type atomic_constraint = 
      {
        term_eq : (variable * (variable list * term)) list;
        termAC_eq : (symbol * (variable list * (term * int) list) * (variable list * (term * int) list)) list
      }

    let string_of_varsterm (vars,t) = 
      Printf.sprintf "[%s] %s" (string_of_list string_of_variable "," vars) (string_of_term t)

    let string_of_varsmterm f (vars,mtl) = 
      Printf.sprintf "[%s] %s" (string_of_list string_of_variable "," vars) (string_of_term_list_multiplicity f mtl)

    let string_of_atomic cons = 
      let str_eq = string_of_list (fun (v,vt) -> Printf.sprintf "%s <> %s" (string_of_variable v) (string_of_varsterm vt)) " || " cons.term_eq in
      let strAC_eq = string_of_list (fun (f,vmt1,vmt2) -> Printf.sprintf "%s <> %s" (string_of_varsmterm f vmt1) (string_of_varsmterm f vmt2)) " || " cons.termAC_eq in
      match cons.term_eq = [], cons.termAC_eq = [] with
      | true, true -> "false"
      | true, false ->  strAC_eq
      | false, true ->  str_eq
      | _ -> str_eq ^ " || " ^ strAC_eq

    let string_of_constraints consl = 
      if consl = []
      then "true"
      else string_of_list (fun cons -> "("^ string_of_atomic cons ^ ")") " && " consl

    let equal_vars_term (vars1,t1) (vars2,t2) = 
      List.length vars1 = List.length vars2 && 
      equal t1 t2

    let equal_vars_mterm_list (vars1,mtl1) (vars2,mtl2) = 
      List.length vars1 = List.length vars2 && 
      List.length mtl1 = List.length mtl2 && 
      List.for_all2 (fun (u1,k1) (u2,k2) -> k1 = k2 && equal u1 u2) mtl1 mtl2
    
    let rec weak_unify term_eq termAC_eq t1 t2 = match t1, t2 with
      | FVar v1, FVar v2 when v1 == v2 -> ()
      | FVar { v_link = FTLink t }, t'
      | t', FVar { v_link = FTLink t } -> weak_unify term_eq termAC_eq t t'
      | FVar v, t 
      | t, FVar v -> 
          let vars_term = unfold_rec_and_get_variables_term t in
          term_eq := (v,vars_term) :: !term_eq
      | FFunc(f1,args1), FFunc(f2,args2) ->
          if f1 != f2 then raise NoMatch;
          List.iter2 (weak_unify term_eq termAC_eq) args1 args2
      | FAC(f1,margs1), FAC(f2,margs2) ->
          if f1 != f2 then raise NoMatch;
          let vars1,margs1' = unfold_rec_and_get_variables_mterms f1 margs1 in
          let vars2,margs2' = unfold_rec_and_get_variables_mterms f1 margs2 in
          
          if not (equal_vars_mterm_list (vars1,margs1') (vars2,margs2'))
          then 
            if vars1 = [] && vars2 = [] 
            then raise NoMatch
            else termAC_eq := (f1,(vars1,margs1'),(vars2,margs2')) :: !termAC_eq
      | _ -> raise NoMatch

    let build_opt f_AC same_remaining_problems remaining_problems = 

      let inside_fun acc f margs1 margs2 = 
        let vars1,margs1' = unfold_rec_and_get_variables_mterms f margs1 in
        let vars2,margs2' = unfold_rec_and_get_variables_mterms f margs2 in
        if equal_vars_mterm_list (vars1,margs1') (vars2,margs2')
        then acc
        else 
          if vars1 = [] && vars2 = []
          then raise NoMatch
          else (f,(vars1,margs1'),(vars2,margs2')) :: acc
      in
      let termAC_eq1 = List.fold_left (fun acc (margs1,margs2) -> inside_fun acc f_AC margs1 margs2) [] same_remaining_problems in
      let termAC_eq2 = List.fold_left (fun acc (f,margs1,margs2) -> inside_fun acc f margs1 margs2) termAC_eq1 remaining_problems in

      try 
        Some 
          {
            term_eq = 
              List.map (fun v -> match v.v_link with
                | FTLink t ->
                    let (vars_t',t') = unfold_rec_and_get_variables_term t in
                    v,(vars_t',t')
                | _ -> failwith "[UnifyMinimal.Constraints] Expecting a link."
              ) !current_bound_vars;
            termAC_eq = termAC_eq2
          }
      with NoMatch -> None

    let wedge consl consl' = List.rev_map consl consl'

    let simplify_mterm f ((vars,margs) as vars_mterm) = 
      if List.exists (fun v -> v.v_link <> NoLink) vars
      then unfold_rec_and_get_variables_mterms f margs
      else vars_mterm
    
    let simplify_atomic_constraint modified cons = 
      let term_eq = ref [] in
      let termAC_eq = ref [] in

      try 
        List.iter (fun ((v,(vars2,t2)) as eq) -> match v.v_link with
          | NoLink -> term_eq := eq :: !term_eq
          | FTLink t1 -> modified := true; weak_unify term_eq termAC_eq t1 t2
          | _ -> failwith "[simplify_atomic_constraint] Unexpected link"
        ) cons.term_eq;

        List.iter (fun (f,vars_mt1,vars_mt2) ->
          let (vars1,_) as vars_mt1' = simplify_mterm f vars_mt1 in
          let (vars2,_) as vars_mt2' = simplify_mterm f vars_mt2 in
          if vars_mt1' != vars_mt2'
          then 
            begin
              modified := true;
              if not (equal_vars_mterm_list vars_mt1' vars_mt2')
              then 
                if vars1 = [] && vars2 = []
                then raise NoMatch
                else termAC_eq := (f,vars_mt1',vars_mt2') :: !termAC_eq
            end
        ) cons.termAC_eq;
        
        if !modified
        then Some { term_eq = !term_eq; termAC_eq = !termAC_eq }
        else Some cons
      with NoMatch -> None

    let simplify_constraints consl = 
      let modified = ref false in
      let consl' =
        List.filter_map (fun cons -> match simplify_atomic_constraint modified cons with 
          | Some cons' ->
              if cons'.term_eq = [] && cons'.termAC_eq = []
              then raise NoMatch
              else Some cons'
          | None -> None 
        ) consl
      in
      if !modified then consl' else consl

  end
    
  module ElementaryNew = 
  struct

    open Flattened

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

    let display_vector_nonewline f_print m = 
      for i = 0 to Array.length m - 1 do 
        Printf.printf "%s  " (f_print m.(i))
      done
      
    (* DFS Hullot Tree *)

    type status =
      | NotVisited
      | Visited
      | Finished

    type vertex = 
      {
        mutable status : status;
        successors : (int (* Index *) * int (** Bit representation *)) list
      }

    type occurence_data = 
      {
        vertex_tbl: vertex Array.t;
        roots: int (** Index *) list
      }

    let display_occurrence_data nb_solutions occur_data = 
      Printf.printf "*** Occurrrence data:\n";
      Printf.printf "Roots: %s\n" (string_of_list string_of_int "; " occur_data.roots);
      Printf.printf "Vertex_tbl:\n";
      Array.iteri (fun i vertex ->
        Printf.printf "  %d -> %s\n" i (string_of_list (fun (j,bit_trans) -> Printf.sprintf "(%d,%s)" j (int2bin nb_solutions bit_trans)) " -- " vertex.successors) 
      ) occur_data.vertex_tbl

    exception FoundCycle

    let check_no_cycle n occur_data subset_bits =

      let rec dfs idx = 
        let vertex = occur_data.vertex_tbl.(idx) in
        match vertex.status with 
        | Finished -> ()
        | Visited -> raise FoundCycle
        | NotVisited ->
            vertex.status <- Visited;
            List.iter (fun (idx,repr_bits) ->
              if subset_bits land repr_bits <> 0
              then dfs idx
            ) vertex.successors;
            vertex.status <- Finished
      in

      try 
        List.iter dfs occur_data.roots;
        List.iter (fun idx -> occur_data.vertex_tbl.(idx).status <- NotVisited) occur_data.roots;
        true
      with FoundCycle -> 
        List.iter (fun idx -> occur_data.vertex_tbl.(idx).status <- NotVisited) occur_data.roots;
        false

    let dfs_hullot_tree f_next n all_bits constants_bits occur_data =
      let init_full_one = -1 lsr (Sys.int_size - n) in
    
      let big_enough subset_bits = List.for_all (fun vi -> subset_bits land vi <> 0) all_bits
      in
      let small_enough subset_bits = 
        List.for_all (fun vi -> (subset_bits land vi) land ((subset_bits land vi) -1) = 0) constants_bits &&
        check_no_cycle n occur_data subset_bits
      in
      
      (* When [sign_greater = true], it corresponds to >. *)
      let rec dfs next_dfs pre a k sign_greater = 
        (* Printf.printf "Dfs pre = %s, a = %s, k = %d, sign_greater = %b\n" (int2bin n pre) (int2bin n a) k sign_greater; *)
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

    let exists_in_hullot_tree n all_bits constants_bits occur_data target_subset_sol =
      let init_full_one = -1 lsr (Sys.int_size - n) in
    
      let big_enough subset_bits = 
        List.for_all (fun vi -> subset_bits land vi <> 0) all_bits &&
        target_subset_sol land subset_bits <> 0
      in
      let small_enough subset_bits = 
        List.for_all (fun vi -> (subset_bits land vi) land ((subset_bits land vi) -1) = 0) constants_bits &&
        check_no_cycle n occur_data subset_bits
      in

      let rec dfs pre a k sign_greater = 
        (* Printf.printf "Dfs pre = %s, a = %s, k = %d, sign_greater = %b\n" (int2bin n pre) (int2bin n a) k sign_greater; *)
        let subset_bits, test = 
          if sign_greater 
          then pre lor a, big_enough (pre lor a)
          else pre, small_enough pre 
        in
        if test
        then 
          if k = 0
          then true
          else 
            let a' = a lsr 1 in
            dfs pre a' (k-1) true || dfs (pre lor (a lxor a')) a' (k-1) false
        else false
      in
    
      dfs 0 init_full_one n true

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
          nb_variables: int;  (** Number of variables in the initial problem *)
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
    
      let display_t store = 
        Array.iteri (fun i elt ->
          if i = Array.length store.elts - 1
          then 
            begin 
              Printf.printf "- Variables :\n";
              List.iter (fun sol ->
                display_vector string_of_int sol;
              ) elt
            end
          else
            begin 
              Printf.printf "- Constant %d:\n" i;
              List.iter (fun sol -> display_vector string_of_int sol) elt
            end
        ) store.elts
        
      let display_t_frozen store = 
        Array.iteri (fun i elt ->
          if i = Array.length store.elts_f - 1
          then 
            begin 
              Printf.printf "- Variables :\n";
              List.iter (fun (sol,defect) ->
                print_string "Sol ";
                display_vector_nonewline (fun (k,b) -> Printf.sprintf "(%d,%b)" k b) sol;
                print_string " with defect ";
                display_vector string_of_int defect;
              ) elt
            end
          else
            begin 
              Printf.printf "- Constant %d:\n" i;
              List.iter (fun (sol,defect) ->
                print_string "Sol ";
                display_vector_nonewline (fun (k,b) -> Printf.sprintf "(%d,%b)" k b) sol;
                print_string " with defect ";
                display_vector string_of_int defect;
              ) elt
            end
        ) store.elts_f
        
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
    
      (* Add the content of store2 in store1 *)
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
          for j = 0 to Array.length storage.elts_t.(i) - 1 do 
            let p' = !p lsl 1 in
            p := if storage.elts_t.(i).(j).(idx) <> 0 then succ p' else p'
          done
        done;
        !p
    
      let generate_bitvector_of_all_constants ground_constants storage =
        let rec loop nb_remaing_solutions idx =
          if idx = storage.nb_constants
          then []
          else
            if ground_constants.(idx) = None
            then
              let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
              let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in
              ((-1 lsr (Sys.int_size - nb_solution_of_constant_idx)) lsl nb_remaing_solutions) :: loop nb_remaing_solutions (idx+1)
            else 
              begin
                (* Printf.printf "Loop nb_remaing_solutions = %d, idx = %d\n" nb_remaing_solutions idx; *)
                let p = ref 0 in
                for i = 0 to storage.nb_constants - 1 do
                  for j = 0 to Array.length storage.elts_t.(i) - 1 do 
                    let p' = !p lsl 1 in
                    p := if storage.elts_t.(i).(j).(idx) <> 0 then succ p' else p'
                  done
                done;
                let full_p = !p lsl Array.length storage.elts_t.(storage.nb_constants) in
                
                let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
                let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in

                (* Printf.printf "Value p: %s, nb_sol_const_idx: %d, nb_remainig: %d, p_pure_idx: %s, p_full: %s\n" 
                  (int2bin storage.nb_elts_t !p) nb_solution_of_constant_idx nb_remaing_solutions
                  (int2bin storage.nb_elts_t p_pure_idx) (int2bin storage.nb_elts_t full_p)
                  ; *)

                full_p :: loop nb_remaing_solutions (idx+1)
              end
        in
        loop storage.nb_elts_t 0
    
      let generate_bitvectors ground_constants storage = 
        let constant_bitvectors = generate_bitvector_of_all_constants ground_constants storage in
        let all_bitvectors = ref constant_bitvectors in
        for idx = storage.nb_constants to storage.nb_constants + storage.nb_variables - 1 do
          all_bitvectors := generate_bitvectors_of_variable storage idx :: !all_bitvectors
        done;
        constant_bitvectors, !all_bitvectors
    
      (** Generation of the occurrence data *)

      let generate_occurrence_data (occur_variables:(int list *int) Array.t) storage =

        let vertex_tbl = Array.make storage.nb_variables { status = NotVisited; successors = [] } in

        let build_transition_bit idx_xi bit_xj =
          (* if !count_unify = 1
            then 
              begin
                Printf.printf "build_transition_bit (%d,%s)\n" idx_xi (int2bin storage.nb_variables bit_xj);
                flush_all ();
              end; *)
          let p = ref 0 in
          for i = 0 to storage.nb_constants - 1 do
            for j = 0 to Array.length storage.elts_t.(i) - 1 do 
              let p' = !p lsl 1 in
              if storage.elts_t.(i).(j).(idx_xi+storage.nb_constants) <> 0 && bit_xj land (snd occur_variables.(i)) <> 0
              then p := succ p'
              else p := p'
            done
          done;
          !p lsl (Array.length storage.elts_t.(storage.nb_constants))
        in

        let roots = ref [] in

        for i = 0 to storage.nb_variables - 1 do
          let bit_xj = ref (1 lsl (storage.nb_variables - 1)) in
          let succ = ref [] in
          for j = 0 to storage.nb_variables - 1 do
            if i <> j 
            then 
              begin
                let transition_bit = build_transition_bit i !bit_xj in
                if transition_bit <> 0
                then succ := (j,transition_bit) :: !succ
              end;
            bit_xj := !bit_xj lsr 1
          done;
          vertex_tbl.(i) <- { status = NotVisited; successors = !succ };
          if !succ <> [] then roots := i :: !roots
        done;

        { vertex_tbl = vertex_tbl; roots = !roots }

      (** Suitable_bitsubset_to_substitutions *)
      let suitable_bitsubset_to_substitution storage f_AC constants variables ground_constants p = 
        
        (* Reset the recorded term in ground_constants *)
        Array.iter (function None -> () | Some ref_t -> ref_t := dummy) ground_constants;

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
                Array.iteri (fun j ground -> match ground with
                  | None -> ()
                  | Some ref_t ->
                      let k = sol.(j) in
                      if k <> 0
                        then 
                          begin
                            if k <> 1 || !ref_t != dummy then failwith "[Elementary.Storage_solutions] The 'smaller than' test should have discarded this case"; 
                            ref_t := storage.associated_variables.(i)
                          end
                ) ground_constants;
                loop_vars (i - 1) (bit_i lsl 1)
              end
        in

        let rec loop_constants i ith_constant constant sols_constant bit_i =
          (* if !count_unify = 1
          then Printf.printf "loop_constants(%d,%d,%s,%s)\n" i ith_constant (Flattened.string_of_term constant) (int2bin storage.nb_elts_t bit_i); *)
          if i = -1
          then bit_i
          else
            if bit_i land p = 0 (* The subset do not contain the solution *)
            then loop_constants (i - 1) ith_constant constant sols_constant (bit_i lsl 1)
            else 
              begin 
                let sol = sols_constant.(i) in
                (* if !count_unify = 1
                then
                  begin 
                    Printf.printf "Sol: ";
                    display_vector string_of_int sol
                  end; *)

                for j = 0 to Array.length term_links -1 do
                  let k = sol.(j+storage.nb_constants) in
                  if k <> 0
                  then term_links.(j) <- (constant,k) :: term_links.(j)
                done;
                Array.iteri (fun j ground -> match ground with
                  | None -> ()
                  | Some ref_t ->
                    if j != ith_constant
                    then 
                      let k = sol.(j) in
                      if k <> 0
                      then 
                        begin
                          (* if !count_unify = 1
                          then
                            begin 
                              Printf.printf "Recording a term with j: %d\n" j
                            end; *)
                          if k <> 1 || !ref_t != dummy then failwith "[Elementary.Storage_solutions] The 'smaller than' test should have discarded this case"; 
                          ref_t := constant
                        end
                ) ground_constants;
                (bit_i lsl (i + 1))
              end
        in
    
        let rec loop_all_constants ith_constant bit_i = 
          (* Printf.printf "loop_all_constants(%d,%s)\n" ith_constant (int2bin storage.nb_elts_t bit_i); *)
          if ith_constant = - 1
          then ()
          else
            let sols_constant = storage.elts_t.(ith_constant) in
            let bit_i' = loop_constants (Array.length sols_constant - 1) ith_constant constants.(ith_constant) sols_constant bit_i in
            loop_all_constants (ith_constant-1) bit_i'
        in
    
        let bit_i = loop_vars (Array.length storage.associated_variables - 1) 1 in
        loop_all_constants (storage.nb_constants - 1) bit_i;
    
        for i = 0 to Array.length variables - 1 do
          match term_links.(i) with
            | [] -> failwith "[suitable_bitsubset_to_substitution] There should be a term to link."
            (* | [FVar ({v_link = NoLink; } as v),1] -> link v (FTLink (FVar variables.(i))) *)
            | [t,1] -> link variables.(i) (FTLink t)
            | mt -> link variables.(i) (FTLink (FAC(f_AC,mt)))
        done
    
      (** Remove *)
      let remove_equation_from_solutions storage idx_constant local_idx_list_to_remove = 
        (* if !count_unify = 1
          then 
            begin 
              Printf.printf "-- remove_equation_from_solutions(%d,[%s]) with Storage:\n"
                idx_constant (string_of_list string_of_int "," local_idx_list_to_remove);
              display storage;
              flush_all ()
            end; *)

        let elts = Array.map Array.copy storage.elts_t in
        let sol_ar = elts.(idx_constant) in
        let nb_elt_to_remove = List.length local_idx_list_to_remove in
        let new_sol_ar = Array.make (Array.length sol_ar - nb_elt_to_remove) sol_ar.(0) in


        let rec loop i new_i = function
          | [] -> for j = 0 to Array.length sol_ar - 1 - i do new_sol_ar.(new_i+j) <- sol_ar.(i+j) done
          | j::q when i = j -> loop (i+1) new_i q
          | l -> 
              new_sol_ar.(new_i) <- sol_ar.(i); 
              loop (i+1) (new_i+1) l
        in

        loop 0 0 local_idx_list_to_remove;
        elts.(idx_constant) <- new_sol_ar;
        (* if !count_unify = 1
          then 
            begin 
              Printf.printf "Completed remove_equation_from_solutions\n";
              flush_all ()
            end; *)
        { storage with elts_t = elts; nb_elts_t = storage.nb_elts_t - nb_elt_to_remove }
    end
    
    (* In [solve_system_diophantine_equations nb_constants matrix_system], we assume that
      then first [nb_constants] columns of [matrix_system] represents constants. *)
    let solve_system_diophantine_equations nb_constants (occur_variables:(int list * int) Array.t) ground_constants matrix_system =
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
        (* if !count_unify = 1
          then 
            begin
              Printf.printf "*** set_Vk_not_in_Mk:\n";
              Storage_solutions.display_t_frozen set_Vk_not_in_Mk;
              Printf.printf "*** set_Vk_in_Mk:\n";
              Storage_solutions.display_t set_Vk_in_Mk;
              Printf.printf "*** set_rest_Mk:\n";
              Storage_solutions.display_t set_rest_Mk;
              print_string "-------\n"
            end; *)

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
                          (* Froze the previous successful index. *)
                          List.iter (fun l ->
                            new_v.(l) <- (fst new_v.(l), true);
                          ) !success_j;

                          (* If j was a non-ground constant, froze the variables that occur in the constant *)
                          if j < nb_constants && ground_constants.(j) <> None
                          then 
                            begin 
                              if fst new_v.(j) <> 1 then failwith "It should be one";
                              new_v.(j) <- (1, true);
                              List.iter (fun k -> new_v.(k) <- (fst new_v.(k), true)) (fst occur_variables.(j))
                            end;

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
      
      (* Initialise the sets *)
      let e_frozen_template = Array.make nb_variables (0,false) in

      (* Froze all the ground ground constants *)
      for j = 0 to nb_constants - 1 do
        if ground_constants.(j) = None
        then e_frozen_template.(j) <- (0,true)
      done;

      let e_frozen_template_ground = Array.copy e_frozen_template in

      for j = 0 to nb_constants - 1 do 
        if is_null initial_defects.(j)
        then 
          let ej = Array.make nb_variables 0 in
          ej.(j) <- 1;
          Storage_solutions.add init_set_Vk_in_Mk (min j nb_constants) ej;
          if ground_constants.(j) = None
          then
            begin
              e_frozen_template.(j) <- (0,true);
              e_frozen_template_ground.(j) <- (0,true)
            end
          else e_frozen_template.(j) <- (0,true)
        else
          begin
            let ej = 
              if ground_constants.(j) = None
              then 
                begin 
                  let ej' = Array.copy e_frozen_template_ground in
                  e_frozen_template.(j) <- (0,true);
                  e_frozen_template_ground.(j) <- (0,true);
                  ej'
                end
              else
                begin 
                  let ej' = Array.copy e_frozen_template in
                  e_frozen_template.(j) <- (0,true);
                  ej'
                end
            in
            ej.(j) <- (1,true);
            (* Froze the variables that occur in the constant *)
            List.iter (fun k -> ej.(k+nb_constants) <- (0,true)) (fst occur_variables.(j));

            Storage_solutions.add_frozen init_set_Vk_not_in_Mk (min j nb_constants) (ej,initial_defects.(j));
          end
      done;
      
      for j = nb_constants to nb_variables - 1 do 
        if is_null initial_defects.(j)
        then 
          let ej = Array.make nb_variables 0 in
          ej.(j) <- 1;
          Storage_solutions.add init_set_Vk_in_Mk (min j nb_constants) ej
        else
          begin
            let ej = Array.copy e_frozen_template in
            ej.(j) <- (1,false);

            Storage_solutions.add_frozen init_set_Vk_not_in_Mk (min j nb_constants) (ej,initial_defects.(j));
          end;
        e_frozen_template.(j) <- (0,true);
      done;
    
      build_M init_set_Vk_not_in_Mk init_set_Vk_in_Mk;
    
      set_rest_Mk
    
    module MatrixGeneration = struct
    
      let dummy_vars = fresh_variable ()
    
      (* Should be improved when the terms will be DAG *)
      type t = 
        {
          mutable vars: (variable * int Array.t) list;
          mutable nb_vars: int;
          mutable constants: (term * bool (* Is ground when true *) * (int list * int) (* Occur variables *) * int Array.t (* Coeffs *)) list;
          mutable nb_constants: int;
          nb_equations: int
        }

      let display storage = 
        Printf.printf "Storage:\n";
        Printf.printf "  Vars = \n";
        List.iter (fun (v,coeffs) -> Printf.printf "    %s with coeff = " (string_of_variable v); display_vector string_of_int coeffs) storage.vars;
        Printf.printf "  Nb_vars = %d\n" storage.nb_vars;
        Printf.printf "  Constants = \n";
        List.iter (fun (t,ground,occur,coeffs) -> 
          Printf.printf "    %s with ground=%b, occur = ([%s],%s) and coeff = " 
            (string_of_term t)
            ground
            (string_of_list string_of_int "," (fst occur))
            (int2bin storage.nb_vars (snd occur))
        
          ; 
          display_vector string_of_int coeffs
        ) storage.constants;
        Printf.printf "  Nb_constants = %d\n" storage.nb_constants;
        Printf.printf "  Nb_equations = %d\n" storage.nb_equations;
        flush_all ()
    
      let create nb_equations = 
        {
          vars = [];
          nb_vars = 0;
          constants = [];
          nb_constants = 0;
          nb_equations = nb_equations
        }
    
      let add_variable store ith_eq v k = 
        let rec loop list_variables = match list_variables with
          | [] -> 
              (* The variable is greater than all *)
              let coeffs = Array.make store.nb_equations 0 in
              coeffs.(ith_eq) <- k;
              store.nb_vars <- store.nb_vars + 1;
              [v,coeffs]
          | ((v',coeffs') as v_coeff)::q_vars ->
              match compare_variable v v' with
              | 0 -> 
                  coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
                  list_variables
              | -1 -> 
                  (* The variable was not recorded *)
                  let coeffs = Array.make store.nb_equations 0 in
                  coeffs.(ith_eq) <- k;
                  store.nb_vars <- store.nb_vars + 1;
                  (v,coeffs) :: list_variables
              | _ -> v_coeff :: loop q_vars
        in
        store.vars <- loop store.vars
    
      let add_constant store t is_ground occur_vars ith_eq k = 
        let rec loop list_constants = match list_constants with
          | [] -> 
              (* The constant is greater than all *)
              let coeffs = Array.make store.nb_equations 0 in
              coeffs.(ith_eq) <- k;
              store.nb_constants <- store.nb_constants + 1;
              [t,is_ground,occur_vars,coeffs]
          | ((t',_,_,coeffs') as t_coeff)::q_const ->
              match compare t t' with
              | 0 -> 
                  coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
                  list_constants
              | -1 -> 
                  (* The variable was not recorded *)
                  let coeffs = Array.make store.nb_equations 0 in
                  coeffs.(ith_eq) <- k;
                  store.nb_constants <- store.nb_constants + 1;
                  (t,is_ground,occur_vars,coeffs) :: list_constants
              | _ -> t_coeff :: loop q_const
        in
        store.constants <- loop store.constants
    
      type link+= ILink of int

      let filter_index_bool bool_ar = 
        let p = ref 0 in
        let rec loop acc i_repr = function
          | -1 -> acc, !p
          | i -> 
              if bool_ar.(i)
              then 
                begin 
                  p := !p lor i_repr; 
                  loop (i::acc) (i_repr lsl 1) (i-1)
                end
              else loop acc (i_repr lsl 1) (i-1)
        in
        loop [] 1 (Array.length bool_ar - 1)

      let unfold_term_with_occur_vars nb_variables t =
        let ground = ref true in
        let occur_variables = Array.make nb_variables false in

        let rec loop t = match t with
          | FVar { v_link = FTLink t; _ } -> loop t
          | FVar { v_link = ILink j; _ } ->
              occur_variables.(j) <- true;
              ground := false;
              t
          | FVar _ -> ground := false; t
          | FFunc(f,args) -> 
              let args' = List.mapq loop args in
              if args == args' then t else FFunc(f,args')
          | FAC(f,margs) -> 
              let margs' = 
                List.mapq (fun ((t,k) as pair)-> 
                  let t' = loop t in
                  if t == t' then pair else (t',k)
                ) margs
              in
              if margs' == margs then t else FAC(f,margs') 
        in

        let t_unfolded = loop t in
        !ground, filter_index_bool occur_variables, t_unfolded

      let get_occur_vars nb_variables t = 
        let occur_variables = Array.make nb_variables false in

        let rec loop t = match t with
          | FVar { v_link = FTLink t; _ } -> loop t
          | FVar { v_link = ILink j; _ } ->
              occur_variables.(j) <- true
          | FVar _ -> ()
          | FFunc(_,args) -> List.iter loop args
          | FAC(_,margs) -> List.iter (fun (t,_) -> loop t) margs 
        in

        loop t;
        filter_index_bool occur_variables

      let cleanup_variables store = 
        let rec loop = function 
          | [] -> []
          | (_,coeffs) as v_data ::q ->
              if Array.for_all (fun i -> i = 0) coeffs
              then 
                begin 
                  store.nb_vars <- store.nb_vars - 1;
                  loop q
                end
              else v_data :: loop q
        in
        store.vars <- loop store.vars

      let cleanup_constants store = 
        let rec loop = function 
          | [] -> []
          | ((_,_,_,coeffs) as t_data) ::q ->
              if Array.for_all (fun i -> i = 0) coeffs
              then 
                begin 
                  store.nb_constants <- store.nb_constants - 1;
                  loop q
                end
              else t_data :: loop q
        in
        store.constants <- loop store.constants

      let cleanup_equations matrix = 
        let empty_equations = ref [] in
        let count_empty_eq = ref 0 in

        for i = 0 to Array.length matrix - 1 do
          if Array.for_all (fun k -> k = 0) matrix.(i)
          then (empty_equations := i :: !empty_equations; incr count_empty_eq)
        done;

        if !empty_equations <> []
        then 
          let new_matrix = Array.make (Array.length matrix - !count_empty_eq) matrix.(0) in
          let rec loop i new_i = function 
            | [] -> for j = 0 to Array.length matrix - 1 - i do new_matrix.(new_i+j) <- matrix.(i+j) done
            | j::q when i = j -> loop (i+1) new_i q
            | l -> 
                new_matrix.(new_i) <- matrix.(i); 
                loop (i+1) (new_i+1) l
          in
          loop 0 0 (List.rev !empty_equations);
          new_matrix
        else matrix

      let from_previous_unification_equations_non_instantiated f_AC matrix_system variables constants occur_variables ground_constants new_equations idx1 idx2 = 

        (* Unfold variables and F_AC *)
        let new_equations = 
          List.map (fun (left_l,right_l) ->
            let new_left_l = ref [] in
            let new_right_l = ref [] in 
            List.iter (unfold_AC_only f_AC new_left_l) left_l;
            List.iter (unfold_AC_only f_AC new_right_l) right_l;
            !new_left_l,!new_right_l
          ) new_equations
        in

        (* Select which constant replace the other one. *)
        let idx_replacing, idx_to_replace = 
          if ground_constants.(idx1) = None || List.length (fst occur_variables.(idx1)) < List.length (fst occur_variables.(idx2))
          then idx1,idx2 
          else idx2,idx1
        in

        let previous_nb_constants = Array.length constants in
        let previous_nb_variables = Array.length variables in
        let previous_nb_equations = Array.length matrix_system in

        let nb_equations = previous_nb_equations + List.length new_equations in
        let store = create nb_equations in

        let non_variable_terms = ref [] in

        (** Add only variables: from matrix *)
        let rec retrieve acc = function
          | -1 -> acc
          | i ->
              let coeffs = Array.make store.nb_equations 0 in
              for j = 0 to previous_nb_equations - 1 do coeffs.(j) <- matrix_system.(j).(previous_nb_constants+i) done;
              retrieve ((variables.(i),coeffs)::acc) (i-1)
        in
        store.vars <- retrieve [] (previous_nb_variables - 1);
        store.nb_vars <- previous_nb_variables;

        (* if !count_unify = 1
        then 
          begin 
            Printf.printf "*** After recording of variables in old_matrix\n.";
            display store;
          end; *)

        (** Add the remaining variables *)
        List.iteri (fun i (left_eq,right_eq) ->
          List.iter (function (t,k) -> match t with
            | FVar v -> add_variable store (i+previous_nb_equations) v k
            | t -> non_variable_terms := (i+previous_nb_equations,t,k) :: !non_variable_terms
          ) left_eq;
          List.iter (function (t,k) -> match t with
            | FVar v -> add_variable store (i+previous_nb_equations) v (-k)
            | t -> non_variable_terms := (i+previous_nb_equations,t,-k) :: !non_variable_terms
          ) right_eq;
        ) new_equations;

        (* if !count_unify = 1
        then 
          begin 
            Printf.printf "*** Before cleanup variables\n.";
            display store;
          end; *)

        cleanup_variables store;

        (* if !count_unify = 1
        then 
          begin 
            Printf.printf "*** After cleanup variables\n.";
            display store;
          end; *)

        (* if !count_unify = 1
        then 
          begin 
            Printf.printf "*** After recording of variables in new_equations\n.";
            display store;
          end; *)

        auto_cleanup_no_catch (fun () ->
          (* Link the variables *)
          List.iteri (fun i (v,_) -> link v (ILink i)) store.vars;

          let nb_variables = store.nb_vars in
            
          (* Add terms from matrix *)
          let rec retrieve acc = function
            | -1 -> acc
            | i when i = idx_to_replace -> 
                retrieve acc (i-1)
            | i when i = idx_replacing ->
                let coeffs = Array.make store.nb_equations 0 in
                for j = 0 to previous_nb_equations - 1 do coeffs.(j) <- matrix_system.(j).(i) + matrix_system.(j).(idx_to_replace) done;
                let (is_ground,occur_vars) = match ground_constants.(i) with
                  | None -> true, ([],0)
                  | Some _ -> false, get_occur_vars nb_variables constants.(i)
                in
                retrieve ((constants.(i),is_ground,occur_vars,coeffs)::acc) (i-1)
            | i ->
                let coeffs = Array.make store.nb_equations 0 in
                for j = 0 to previous_nb_equations - 1 do coeffs.(j) <- matrix_system.(j).(i) done;
                let (is_ground,occur_vars) = match ground_constants.(i) with
                  | None -> true, ([],0)
                  | Some _ -> false, get_occur_vars nb_variables constants.(i)
                in
                retrieve ((constants.(i),is_ground,occur_vars,coeffs)::acc) (i-1)
          in
          store.constants <- retrieve [] (previous_nb_constants - 1);
          store.nb_constants <- previous_nb_constants - 1;


          (* Add terms from new_equations *)
          List.iter (fun (ith_eq,t,k) ->
            let (is_ground,occur_vars,t_unfolded) = unfold_term_with_occur_vars nb_variables t in
            add_constant store t_unfolded is_ground occur_vars ith_eq k
          ) !non_variable_terms;


          (* if !count_unify = 1
          then 
            begin 
              Printf.printf "*** Before cleanup constants\n.";
              display store;
            end; *)

          cleanup_constants store;

          (* if !count_unify = 1
          then 
            begin 
              Printf.printf "*** After cleanup constants\n.";
              display store;
            end; *)
        );

        (* if !count_unify = 1
        then 
          begin 
            Printf.printf "*** After recording of terms in new_equations\n.";
            display store;
          end; *)

        let matrix = Array.make_matrix store.nb_equations (store.nb_constants + store.nb_vars) 0 in
        let variables = Array.make store.nb_vars dummy_vars in
        let constants = Array.make store.nb_constants dummy in
        let occur_variables = Array.make store.nb_constants ([],0) in
        let ground_constants = Array.make store.nb_constants None in

        (* Register the variables *)
        List.iteri (fun j (v,coeffs) ->
          variables.(j) <- v;
          Array.iteri (fun i k ->
            matrix.(i).(store.nb_constants+j) <- k
          ) coeffs  
        ) store.vars;

        (* Register the constants *)
        List.iteri (fun j (t,is_ground,occur_vars,coeffs) ->
          constants.(j) <- t;
          occur_variables.(j) <- occur_vars;
          if not is_ground then ground_constants.(j) <- Some (ref dummy);
          Array.iteri (fun i k ->
            matrix.(i).(j) <- k
          ) coeffs  
        ) store.constants;

        (cleanup_equations matrix,variables,store.nb_vars,constants,store.nb_constants,occur_variables,ground_constants)

      let from_unification_equations f_AC system_equations = 
        if system_equations = []
        then failwith "[Flattened.Elementary.MatrixGeneration.from_matching_equations] The system of equations should not be empty";

        let nb_equations = List.length system_equations in
        let store = create nb_equations in

        (* Unfold variables and F_AC *)
        let system_equations = 
          List.map (fun (left_l,right_l) ->
            let new_left_l = ref [] in
            let new_right_l = ref [] in 
            List.iter (unfold_AC_only f_AC new_left_l) left_l;
            List.iter (unfold_AC_only f_AC new_right_l) right_l;
            !new_left_l,!new_right_l
          ) system_equations
        in

        (* if !count_unify = 1
        then 
          begin
            Printf.printf "from_unification_equations: After unfolding\n";
            List.iter (fun (mtl1,mtl2) ->
              Printf.printf "  %s = %s\n"
                (string_of_list (fun (t,k) -> Printf.sprintf "(%s,%d)" (string_of_term t) k) ", " mtl1)
                (string_of_list (fun (t,k) -> Printf.sprintf "(%s,%d)" (string_of_term t) k) ", " mtl2)
            ) system_equations
          end; *)

        let non_variable_terms = ref [] in

        (* Unfold variable link and f_AC *)

        (* Add only variables *)
        List.iteri (fun i (left_eq,right_eq) ->
          List.iter (function (t,k) -> match t with
            | FVar v -> add_variable store i v k
            | t -> non_variable_terms := (i,t,k) :: !non_variable_terms
          ) left_eq;
          List.iter (function (t,k) -> match t with
            | FVar v -> add_variable store i v (-k)
            | t -> non_variable_terms := (i,t,-k) :: !non_variable_terms
          ) right_eq;
        ) system_equations;

        cleanup_variables store;

        auto_cleanup_no_catch (fun () ->
          (* Link the variables *)
          List.iteri (fun i (v,_) -> link v (ILink i)) store.vars;

          let nb_variables = store.nb_vars in
            
          (* Add terms *)
          List.iter (fun (ith_eq,t,k) ->
            let (is_ground,occur_vars,t_unfolded) = unfold_term_with_occur_vars nb_variables t in
            add_constant store t_unfolded is_ground occur_vars ith_eq k
          ) !non_variable_terms;

          cleanup_constants store
        );

        let matrix = Array.make_matrix store.nb_equations (store.nb_constants + store.nb_vars) 0 in
        let variables = Array.make store.nb_vars dummy_vars in
        let constants = Array.make store.nb_constants dummy in
        let occur_variables = Array.make store.nb_constants ([],0) in
        let ground_constants = Array.make store.nb_constants None in

        (* Register the variables *)
        List.iteri (fun j (v,coeffs) ->
          variables.(j) <- v;
          Array.iteri (fun i k ->
            matrix.(i).(store.nb_constants+j) <- k
          ) coeffs  
        ) store.vars;

        (* Register the constants *)
        List.iteri (fun j (t,is_ground,occur_vars,coeffs) ->
          constants.(j) <- t;
          occur_variables.(j) <- occur_vars;
          if not is_ground then ground_constants.(j) <- Some (ref dummy);
          Array.iteri (fun i k ->
            matrix.(i).(j) <- k
          ) coeffs  
        ) store.constants;

        (cleanup_equations matrix,variables,store.nb_vars,constants,store.nb_constants,occur_variables,ground_constants)

      let from_previous_unification_equations_instantiated f_AC matrix_system  variables constants occur_variables ground_constants new_equations idx1 idx2 = 
        (* Select which constant replace the other one. *)
        let idx_replacing, idx_to_replace = 
          if ground_constants.(idx1) = None || List.length (fst occur_variables.(idx1)) < List.length (fst occur_variables.(idx2))
          then idx1,idx2 
          else idx2,idx1
        in

        let acc_equations = ref new_equations in
        let width_matrix =  Array.length matrix_system.(0) - 1 in
        let nb_constants = Array.length constants in
        
        (* if !count_unify = 1
          then 
            begin
              Printf.printf "New equations\n";
              List.iter (fun (mtl1,mtl2) ->
                Printf.printf "  %s = %s\n"
                  (string_of_list (fun (t,k) -> Printf.sprintf "(%s,%d)" (string_of_term t) k) ", " mtl1)
                  (string_of_list (fun (t,k) -> Printf.sprintf "(%s,%d)" (string_of_term t) k) ", " mtl2)
              ) new_equations
            end; *)

        for i = 0 to Array.length matrix_system - 1 do
          let left_eq = ref [] in
          let right_eq = ref [] in
          for j = 0 to width_matrix do 
            if j = idx_to_replace
            then ()
            else 
              let term = if j >= nb_constants then FVar (variables.(j-nb_constants)) else constants.(j) in
              let coeff = 
                if j = idx_replacing 
                then matrix_system.(i).(j) + matrix_system.(i).(idx_to_replace) 
                else matrix_system.(i).(j) 
              in
              if coeff  > 0 then left_eq := (term,coeff) :: !left_eq 
              else if coeff = 0 then ()
              else right_eq := (term,-coeff) :: !right_eq 
          done;
          acc_equations := (!left_eq,!right_eq) :: !acc_equations
        done;

        (* if !count_unify = 1
        then 
          begin
            Printf.printf "New system of equations\n";
            List.iter (fun (mtl1,mtl2) ->
              Printf.printf "  %s = %s\n"
                (string_of_list (fun (t,k) -> Printf.sprintf "(%s,%d)" (string_of_term t) k) ", " mtl1)
                (string_of_list (fun (t,k) -> Printf.sprintf "(%s,%d)" (string_of_term t) k) ", " mtl2)
            ) !acc_equations
          end; *)

        from_unification_equations f_AC !acc_equations
    end 
    
    let rec unify_equations_of_terms f_no_equation f_unify neg_constraint_list remaining_problems matrix_system variables f_AC ground_constants constants occur_variables solutions = 
      if !count_unify = 1
      then 
        begin 
          Printf.printf "\n*** Unification_of_terms\n";
          print_string "Matrix =\n";
          display_matrix string_of_int matrix_system;
          Printf.printf "Variables (%d) = " (Array.length variables);
          display_vector string_of_variable variables;
          Printf.printf "Constants (%d) = " (Array.length constants);
          display_vector string_of_term constants;
          Printf.printf "Remaining problems: %s\n" 
            (string_of_list (fun (f,mt1,mt2) -> Printf.sprintf "%s = %s" (string_of_term_list_multiplicity f mt1) (string_of_term_list_multiplicity f mt2)) " && " remaining_problems);
          Printf.printf "Constraints: %s\n" (Constraints.string_of_constraints neg_constraint_list);
          Printf.printf "Solution with potential equations\n";
          Storage_solutions.display solutions;
          flush_all ();
        end;
      
      (* if !count_unify = 1
      then 
        begin 
          Printf.printf "** Unification_of_terms\n";
          Printf.printf "  Constraints: %s\n" (Constraints.string_of_constraints neg_constraint_list);
          Printf.printf "  Solution with potential equations\n";
          Storage_solutions.display solutions;
          flush_all ()
        end; *)
      
      if solutions.Storage_solutions.nb_elts_t = 0 then raise NoMatch;

      let nb_constants = Array.length constants in
      let nb_constants_solution = solutions.Storage_solutions.nb_elts_t - Array.length solutions.Storage_solutions.elts_t.(nb_constants) in
      let count_sol = ref nb_constants_solution in

      (* if !count_unify = 1
        then 
          begin 
            Printf.printf "  nb_constants = %d, nb_constants_solution = %d\n" nb_constants nb_constants_solution;
            flush_all ()
          end; *)

      (* Find all solutions with same equation *)
      let rec find_all_solutions idx_constant2 ar_sol list_subset bit_repr bit_subset i = 
        (* if !count_unify = 1
        then 
          begin 
            Printf.printf "find_all_solutions(%d,[%s],%s,%s,%d) with count_sol = %d " idx_constant2 (string_of_list string_of_int "," list_subset) (int2bin solutions.nb_elts_t bit_repr) (int2bin solutions.nb_elts_t bit_subset) i !count_sol;
            flush_all ()
          end; *)

        match i with
        | -1 -> list_subset, bit_subset
        | i -> 
            if ar_sol.(i).(idx_constant2) <> 0
            then 
              (* Found the equation *)
              find_all_solutions idx_constant2 ar_sol (i::list_subset) (bit_repr lsl 1) (bit_repr lor bit_subset) (i-1)
            else
              (* No Equation *)
              find_all_solutions idx_constant2 ar_sol list_subset (bit_repr lsl 1) bit_subset (i-1)
      in

      (* Find equation *)
      let rec find_in_solution idx_constant sol i = 
        (* if !count_unify = 1
          then 
            begin 
              Printf.printf "find_in_solution(%d,%d) with count_sol = %d and solution " idx_constant i !count_sol;
              display_vector string_of_int sol;
              flush_all ()
            end; *)
        match i with
        | -1 -> None 
        | i -> 
            if sol.(i) <> 0 && i <> idx_constant
            then Some i
            else find_in_solution idx_constant sol (i-1)
      in

      let rec find_equation_in_constant idx_constant1 = 
        (* if !count_unify = 1
          then 
            begin 
              Printf.printf "find_equation_in_constant(%d)\n" idx_constant1;
              flush_all ()
            end; *)
        if idx_constant1 = -1
        then None 
        else
          let ar = solutions.Storage_solutions.elts_t.(idx_constant1) in
          let rec rev_find = function
            | - 1 -> None
            | i ->
                let sol = ar.(i) in
                decr count_sol;
                match find_in_solution idx_constant1 sol (nb_constants - 1) with
                | None -> rev_find (i-1)
                | Some(idx_constant2) -> 
                    (* We found an equation. Look for all solutions that satisfy this equation *)
                    let bit_subset = 1 lsl (solutions.Storage_solutions.nb_elts_t - 1 - !count_sol) in
                    let bit_repr = bit_subset lsl 1 in
                    let eq_list_subset, eq_bit_subset = find_all_solutions idx_constant2 ar [i] bit_repr bit_subset (i-1) in
                    Some(idx_constant1,idx_constant2,eq_list_subset,eq_bit_subset)
          in
          match rev_find (Array.length ar - 1) with
          | None -> find_equation_in_constant (idx_constant1 - 1)
          | Some x -> Some x
      in

      let equation_op = find_equation_in_constant (nb_constants - 1) in

      (* if !count_unify = 1
        then 
          begin 
            Printf.printf "** Find equation in constant \n";
          end; *)

      match equation_op with
      | None -> f_no_equation neg_constraint_list remaining_problems solutions
      | Some(idx1,idx2,eq_list_subset,eq_bit_subset) ->
          (* if !count_unify = 1
          then 
            begin 
              Printf.printf "Found equation with (%d,%d,[%s],%s)\n" idx1 idx2 (string_of_list string_of_int "," eq_list_subset) (int2bin solutions.nb_elts_t eq_bit_subset);
              flush_all ()
            end; *)

          (* Bit presentation to subset of solutions *)
          let (constant_bitvectors,all_bitvectors) = Storage_solutions.generate_bitvectors ground_constants solutions in

          (* Occurrence data *)
          let occurence_data = Storage_solutions.generate_occurrence_data occur_variables solutions in

          (* if !count_unify = 1
            then 
              begin 
                Printf.printf "\n** Constant bitvectors\n";
                List.iter (fun p ->
                  Printf.printf "bit = %s\n" (int2bin solutions.nb_elts_t p)
                ) constant_bitvectors;
                Printf.printf "\n** All bitvectors\n";
                List.iter (fun p ->
                  Printf.printf "bit = %s\n" (int2bin solutions.nb_elts_t p)
                ) all_bitvectors;
                display_occurrence_data solutions.nb_elts_t occurence_data;
                flush_all ();
              end; *)

          (* Looking for an existing solution with [eq_bit_subset] *)
          if exists_in_hullot_tree solutions.Storage_solutions.nb_elts_t all_bitvectors constant_bitvectors occurence_data eq_bit_subset 
          then
            let neg_constraint = ref None in
            (* We unify the terms *)
            try 
              auto_cleanup (fun () ->
                if !count_unify = 1
                then 
                  begin 
                    Printf.printf "Equation to be unified: %s = %s\n" (string_of_term constants.(idx1)) (string_of_term constants.(idx2));
                    flush_all ();
                  end;
                let remain_ref_same = ref [] in
                let remain_ref_other = ref [] in
                unify_term_aux_split f_AC remain_ref_same remain_ref_other constants.(idx1) constants.(idx2);
                neg_constraint := Constraints.build_opt f_AC !remain_ref_same !remain_ref_other;
                if !current_bound_vars = []
                then 
                  (* No new unification *)
                  f_unify neg_constraint_list !remain_ref_same (List.rev_append !remain_ref_other remaining_problems) idx1 idx2 false
                else 
                  (* Some variables where instantiated *)
                  f_unify (Constraints.simplify_constraints neg_constraint_list) !remain_ref_same (List.rev_append !remain_ref_other remaining_problems) idx1 idx2 true
              )
            with NoMatch -> 
              (* Unification when the terms are different *) 
              (* if !count_unify = 1
              then 
                begin 
                  Printf.printf "Terms are different\n";
                  Printf.printf "  Constraints: %s\n" (Constraints.string_of_constraints neg_constraint_list);
                  Printf.printf "  Solution with potential equations\n";
                  Storage_solutions.display solutions;
                  flush_all ()
                end; *)
              match !neg_constraint with 
              | None -> 
                  (* if !count_unify = 1 then Printf.printf "No constraint\n"; *)
                  let solutions_filtered = Storage_solutions.remove_equation_from_solutions solutions idx1 eq_list_subset in
                  unify_equations_of_terms f_no_equation f_unify neg_constraint_list remaining_problems matrix_system variables f_AC ground_constants constants occur_variables solutions_filtered
              | Some cons ->
                  (* if !count_unify = 1 then Printf.printf "Constaint: %s\n" (Constraints.string_of_atomic cons); *)
                  if cons.term_eq = [] && cons.termAC_eq = []
                  then raise NoMatch
                  else                
                    let solutions_filtered = Storage_solutions.remove_equation_from_solutions solutions idx1 eq_list_subset in
                    unify_equations_of_terms f_no_equation f_unify (cons::neg_constraint_list) remaining_problems matrix_system variables f_AC ground_constants constants occur_variables   solutions_filtered
          else
            (* No solution exists with *)
            (* let _ = if !count_unify = 1 then Printf.printf "No solution exists\n" in *)
            let solutions_filtered = Storage_solutions.remove_equation_from_solutions solutions idx1 eq_list_subset in
            unify_equations_of_terms f_no_equation f_unify neg_constraint_list remaining_problems matrix_system variables f_AC  ground_constants constants occur_variables solutions_filtered

    let solve f_next f_unify neg_constraint_list remaining_problems f_AC matrix_system variables nb_variables constants nb_constants occur_variables ground_constants =
      if !count_unify = 1
      then 
        begin 
          print_string "Matrix =\n";
          display_matrix string_of_int matrix_system;
          Printf.printf "Variables (%d) = " nb_variables;
          display_vector string_of_variable variables;
          Printf.printf "Constants (%d) = " nb_constants;
          display_vector string_of_term constants;
          Printf.printf "Occur_variables = ";
          display_vector (fun (l,bit) -> Printf.sprintf "([%s],%s)" (string_of_list string_of_int ";" l) (int2bin nb_variables bit)) occur_variables;
          Printf.printf "Ground constants = ";
          display_vector (function None -> "true" | _ -> "false") ground_constants;
          flush_all ();
        end;
      
      if nb_variables = 0 && nb_constants = 0 
      then 
        (* The system is trivially true *)
        f_next neg_constraint_list remaining_problems
      else
        begin 
          (* Solving the matrix system *)
          let solutions = solve_system_diophantine_equations nb_constants occur_variables ground_constants matrix_system in
          let nb_solutions = solutions.Storage_solutions.nb_elts in
          
          if nb_solutions > Sys.int_size - 2
          then failwith "Limit on the number of solutions reached";
        
          if nb_solutions = 0 then raise NoMatch;
        
          let finalized_solutions = Storage_solutions.finalize nb_constants nb_variables solutions in
        
          unify_equations_of_terms (fun neg_constraint_list' remaining_problems' solutions' ->
            (* What we do when there is no more equation in the solutions *)
            (* if !count_unify = 1
            then 
              begin 
                Printf.printf "\n** Finalized solution with no Equations\n";
                Storage_solutions.display solutions';
                flush_all ();
              end; *)

            let nb_solutions = solutions'.Storage_solutions.nb_elts_t in

            (* Bit presentation to subset of solutions *)
            let (constant_bitvectors,all_bitvectors) = Storage_solutions.generate_bitvectors ground_constants solutions' in
            let occurence_data = Storage_solutions.generate_occurrence_data occur_variables solutions' in

            (* if !count_unify = 1
            then 
              begin 
                Printf.printf "\n** Constant bitvectors\n";
                List.iter (fun p ->
                  Printf.printf "bit = %s\n" (int2bin nb_solutions p)
                ) constant_bitvectors;
                Printf.printf "\n** All bitvectors\n";
                List.iter (fun p ->
                  Printf.printf "bit = %s\n" (int2bin nb_solutions p)
                ) all_bitvectors;
                display_occurrence_data solutions'.nb_elts_t occurence_data;
                flush_all ();
              end; *)

            dfs_hullot_tree (fun f_next_dfs p ->
              try 
                auto_cleanup_noreset (fun () ->
                  if !count_unify = 1
                  then 
                    begin
                      Printf.printf "Building the substitution %d with %s\n\n\n" !count_subst (int2bin nb_solutions p);
                      flush_all ()
                    end;
                  Storage_solutions.suitable_bitsubset_to_substitution solutions' f_AC constants variables ground_constants p;
                  f_next neg_constraint_list' remaining_problems'
                )
              with NoMatch -> f_next_dfs ()
            ) nb_solutions all_bitvectors constant_bitvectors occurence_data
          
          ) f_unify neg_constraint_list remaining_problems matrix_system variables f_AC ground_constants constants occur_variables finalized_solutions
        end

    let rec unification f_next neg_constraint_list remaining_problems f_AC system_equations = 
      
      let rec loop neg_constraint_list remaining_problems (matrix_system,variables,nb_variables,constants,nb_constants,occur_variables,ground_constants) = 
        solve (fun neg_constraint_list' remaining_problems' ->
          (* if !count_unify = 1
          then Printf.printf "Solve sucess - creating the next equations\n"; *)
          let new_equations = ref [] in

          for i = 0 to nb_constants - 1 do
            match ground_constants.(i) with
            | None -> ()
            | Some ref_t ->
                if !ref_t != dummy then new_equations := (constants.(i),!ref_t) :: !new_equations
          done;

          f_next neg_constraint_list' remaining_problems' !new_equations
        ) (fun neg_constraint_list' remaing_problems_same remaining_problems' idx1 idx2 vars_instantiated -> 
            (* if !count_unify = 1
            then Printf.printf "Solve - Another round - creating the next matrix\n"; *)
            (* Creating the new matrix *)
            if vars_instantiated
            then loop neg_constraint_list' remaining_problems' (MatrixGeneration.from_previous_unification_equations_instantiated f_AC matrix_system variables constants occur_variables ground_constants remaing_problems_same idx1 idx2)
            else loop neg_constraint_list' remaining_problems' (MatrixGeneration.from_previous_unification_equations_non_instantiated f_AC matrix_system variables constants occur_variables ground_constants remaing_problems_same idx1 idx2)
        ) neg_constraint_list remaining_problems f_AC matrix_system variables nb_variables constants nb_constants occur_variables ground_constants
      in
      loop neg_constraint_list remaining_problems (MatrixGeneration.from_unification_equations f_AC system_equations)
      
  end

  let rec flatten_term f mlist t k = match t with
    | FVar { v_link = FTLink ((FVar _) as t') } -> flatten_term f mlist t' k
    | FVar { v_link = FTLink (FAC(f',margs')); _ } when f == f' ->
        List.fold_left (fun acc_mlist (t',k') ->
          flatten_term f acc_mlist t' (k*k')
        ) mlist margs'
    | FVar { v_link = FTLink t'; _ } -> add_multiplicity f t' k mlist
    | FAC(f',margs') when f == f' -> 
        List.fold_left (fun acc_mlist (t',k') ->
          flatten_term f acc_mlist t' (k*k')
        ) mlist margs'
    | _ -> add_multiplicity f t k mlist

  let flatten_mterm_list f mlist = 
    List.fold_left (fun acc_mlist (t,k) ->
      flatten_term f acc_mlist t k
    ) [] mlist

  let rec partition_remaining_problems f_target = function
    | [] -> [], []
    | (f,mlist1,mlist2) :: q when f == f_target ->
        let same_f_problems, other_problems = partition_remaining_problems f_target q in
        (flatten_mterm_list f_target mlist1,flatten_mterm_list f_target mlist2)::same_f_problems, other_problems
    | pbl::q -> 
        let same_f_problems, other_problems = partition_remaining_problems f_target q in
        same_f_problems, pbl::other_problems

  let rec solve_remaining_problems f_next neg_constraint_list remaining_problems = match remaining_problems with
    | [] -> 
        if !count_unify = 1 then Printf.printf "*** Final constraints: %s\n" (Constraints.string_of_constraints neg_constraint_list);
        let _ = Constraints.simplify_constraints neg_constraint_list in 
        f_next ()
    | (f,_,_) :: _ ->
        let same_f_problems, other_problems = partition_remaining_problems f remaining_problems in
        if same_f_problems = [] then failwith "[Unify.solve_remaining_problems] There should be at least one problem corresponding to the function symbol.";
        ElementaryNew.unification (fun neg_constraint_list' remaining_problems' new_equations ->
          if !count_unify = 1
          then 
            begin
              Printf.printf "After ElementaryNew.unification \n";
              let subst = 
                List.fold_left (fun acc v -> match v.v_link with 
                  | FTLink t -> (v,Flattened.copy_term_rec t)::acc
                  | NoLink -> acc
                  | _ -> failwith "[matching_one] Unexpected case"
                ) [] !current_bound_vars
              in
              Printf.printf "Current subst = %s\n" (string_of_subst subst);
              Printf.printf "New equations : %s\n" (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " new_equations);
              flush_all ();
            end;
          auto_cleanup_noreset (fun () ->
            let remain_ref = ref remaining_problems' in
            List.iter (fun (t1,t2) -> unify_term_aux remain_ref t1 t2) new_equations;
            solve_remaining_problems f_next (Constraints.simplify_constraints neg_constraint_list') !remain_ref  
          )
        ) neg_constraint_list other_problems f same_f_problems

  let unify f_next eq_list = 
    incr count_unify;
    if !count_unify = 1
      then 
        begin
          Printf.printf "Unification %d of %s\n"
            !count_unify 
            (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
          flush_all ();
        end;
    let vars = get_variables_in_equations eq_list in
    auto_cleanup (fun () ->
      let remain_ref = ref [] in
      List.iter (fun (t1,t2) ->
        unify_term_aux remain_ref t1 t2
      ) eq_list;
      solve_remaining_problems (fun () ->
        let subst = 
          List.fold_left (fun acc v -> match v.v_link with 
            | FTLink t -> (v,Flattened.copy_term_rec t)::acc
            | NoLink -> acc
            | _ -> failwith "[matching_one] Unexpected case"
          ) [] vars
        in
        f_next subst
      ) [] !remain_ref
    )

  let verify_unifier eq_list subst =
    if not (List.for_all (fun (t1,t2) ->
        let t1' = apply_subst subst t1 in
        let t2' = apply_subst subst t2 in
        equal t1' t2'
      ) eq_list)
    then
      begin
        begin 
          Printf.printf "*** Problem %d: Found a wrong unifier %s\n"
            !count_unify
              (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
          Printf.printf "- Subst = %s\n" (string_of_subst subst);
          failwith "Error"
        end
      end

  (* Does there exists \theta such that x subst2 =AC x subst1\theta for all variables x of the problems *)
  let subst_implies vars subst1 subst2 =
    let list1 = List.map (fun v -> apply_subst subst1 (FVar v)) vars in
    let list2 = List.map (fun v -> apply_subst subst2 (FVar v)) vars in

    find_matching_term_list list1 list2

  let is_subst_implies vars subst1 subst2 =
    let list1 = List.map (fun v -> apply_subst subst1 (FVar v)) vars in
    let list2 = List.map (fun v -> apply_subst subst2 (FVar v)) vars in

    None <> find_matching_term_list list1 list2

  let verify_minimality str eq_list subst_list =
    let header_printed = ref false in
    let vars = get_variables_in_equations eq_list in

    let rec loop visited_subst = function 
      | [] -> visited_subst
      | subst :: q_subst ->
          if List.exists (fun subst' -> is_subst_implies vars subst' subst) visited_subst
          then loop visited_subst q_subst
          else loop (subst :: (List.filter_rev (fun subst' -> not (is_subst_implies vars subst subst')) visited_subst)) q_subst
    in
    let minmal_set = loop [] subst_list in
    let minimal_set_size = List.length minmal_set in
    let set_size = List.length subst_list in

    if minimal_set_size <> set_size
    then 
      begin 
        header_printed := true;
        Printf.printf "*** Unification %d (%s) not minimal in %s\n"
          !count_unify str
          (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
        Printf.printf "  Number of substitutions in original set: %d\n" set_size;
        Printf.printf "  Number of substitutions in minimal set: %d\n" minimal_set_size;
        Printf.printf "  Gain: %d\n" (set_size - minimal_set_size);
        Printf.printf "  Original set:\n";
        List.iteri (fun i subst -> Printf.printf "   Subst %d = %s\n" i (string_of_subst subst)) subst_list;
        Printf.printf "  Minimal set:\n";
        List.iteri (fun i subst -> Printf.printf "   Subst %d = %s\n" i (string_of_subst subst)) minmal_set;
      end
    
  let verify_correctness eq_list subst_maude_l subst_native_l = 
    let vars = get_variables_in_equations eq_list in
    let header_printed = ref false in
    let correct = ref true in

    let display (i2,subst2) =
      if not !header_printed
        then 
          begin 
            header_printed := true;
            Printf.printf "*** Unification %d incorrect in %s\n"
              !count_unify 
              (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
          end;
        Printf.printf "- Subst_%d = %s\n" i2 (string_of_subst subst2)
    in

    let rec loop i = function 
      | [] -> ()
      | subst :: q_subst ->
          if 
            List.for_all (fun subst_native ->
              match subst_implies vars subst_native subst with 
              | None -> true
              | _ -> false
            ) subst_native_l
          then 
            begin 
              display (i,subst);
              correct := false
            end;
          loop (i+1) q_subst
    in

    loop 1 subst_maude_l;
    !correct

end
  
module UnifyMinimal2 = 
struct
  
  open Flattened

  let rec occurs_check x = function
    | FVar { v_link = FTLink t; _} -> occurs_check x t
    | FVar y -> if x == y then raise NoMatch
    | FFunc(_,args) -> List.iter (occurs_check x) args
    | FAC(_,margs) -> List.iter (fun (t,_) -> occurs_check x t) margs 

  let rec unify_term_aux remaining_problems t1 t2 = match t1, t2 with 
    | FVar v1, FVar v2 when v1 == v2 -> ()
    | FVar { v_link = FTLink t; _}, t' 
    | t', FVar { v_link = FTLink t; _} -> unify_term_aux remaining_problems t t'
    | FVar v1, FVar v2 -> link v1 (FTLink t2)
    | FVar v, t 
    | t, FVar v -> 
        occurs_check v t;
        link v (FTLink t)
    | FFunc(f1,args1), FFunc(f2,args2) -> 
        if f1 != f2 then raise NoMatch;
        List.iter2 (unify_term_aux remaining_problems) args1 args2
    | FAC(f1,margs1), FAC(f2,margs2) ->
        if f1 != f2 then raise NoMatch;
        remaining_problems :=  (f1,margs1,margs2)::!remaining_problems
    | _ -> raise NoMatch

  let rec unify_term_aux_split f_AC same_remaining_problems remaining_problems t1 t2 = match t1, t2 with 
    | FVar v1, FVar v2 when v1 == v2 -> ()
    | FVar { v_link = FTLink t; _}, t' 
    | t', FVar { v_link = FTLink t; _} -> unify_term_aux_split f_AC same_remaining_problems remaining_problems t t'
    | FVar v1, FVar v2 -> link v1 (FTLink t2)
    | FVar v, t 
    | t, FVar v -> 
        occurs_check v t;
        link v (FTLink t)
    | FFunc(f1,args1), FFunc(f2,args2) -> 
        if f1 != f2 then raise NoMatch;
        List.iter2 (unify_term_aux_split f_AC same_remaining_problems remaining_problems) args1 args2
    | FAC(f1,margs1), FAC(f2,margs2) ->
        if f1 != f2 then raise NoMatch;
        if f1 == f_AC
        then same_remaining_problems := (margs1,margs2) :: !same_remaining_problems
        else remaining_problems :=  (f1,margs1,margs2) :: !remaining_problems
    | _ -> raise NoMatch

  module Constraints =
  struct

    type atomic_constraint = 
      {
        term_eq : (variable * (variable list * term)) list;
        termAC_eq : (symbol * (variable list * (term * int) list) * (variable list * (term * int) list)) list
      }

    type t = atomic_constraint list

    let is_false cons = cons.term_eq = [] && cons.termAC_eq = []

    let string_of_varsterm (vars,t) = 
      Printf.sprintf "[%s] %s" (string_of_list string_of_variable "," vars) (string_of_term t)

    let string_of_varsmterm f (vars,mtl) = 
      Printf.sprintf "[%s] %s" (string_of_list string_of_variable "," vars) (string_of_term_list_multiplicity f mtl)

    let string_of_atomic cons = 
      let str_eq = string_of_list (fun (v,vt) -> Printf.sprintf "%s <> %s" (string_of_variable v) (string_of_varsterm vt)) " || " cons.term_eq in
      let strAC_eq = string_of_list (fun (f,vmt1,vmt2) -> Printf.sprintf "%s <> %s" (string_of_varsmterm f vmt1) (string_of_varsmterm f vmt2)) " || " cons.termAC_eq in
      match cons.term_eq = [], cons.termAC_eq = [] with
      | true, true -> "false"
      | true, false ->  strAC_eq
      | false, true ->  str_eq
      | _ -> str_eq ^ " || " ^ strAC_eq

    let string_of_constraints consl = 
      if consl = []
      then "true"
      else string_of_list (fun cons -> "("^ string_of_atomic cons ^ ")") " && " consl

    let equal_vars_term (vars1,t1) (vars2,t2) = 
      List.length vars1 = List.length vars2 && 
      equal t1 t2

    let equal_vars_mterm_list (vars1,mtl1) (vars2,mtl2) = 
      List.length vars1 = List.length vars2 && 
      List.length mtl1 = List.length mtl2 && 
      List.for_all2 (fun (u1,k1) (u2,k2) -> k1 = k2 && equal u1 u2) mtl1 mtl2
    
    let rec weak_unify term_eq termAC_eq t1 t2 = match t1, t2 with
      | FVar v1, FVar v2 when v1 == v2 -> ()
      | FVar { v_link = FTLink t }, t'
      | t', FVar { v_link = FTLink t } -> weak_unify term_eq termAC_eq t t'
      | FVar v, t 
      | t, FVar v -> 
          let vars_term = unfold_rec_and_get_variables_term t in
          term_eq := (v,vars_term) :: !term_eq
      | FFunc(f1,args1), FFunc(f2,args2) ->
          if f1 != f2 then raise NoMatch;
          List.iter2 (weak_unify term_eq termAC_eq) args1 args2
      | FAC(f1,margs1), FAC(f2,margs2) ->
          if f1 != f2 then raise NoMatch;
          let vars1,margs1' = unfold_rec_and_get_variables_mterms f1 margs1 in
          let vars2,margs2' = unfold_rec_and_get_variables_mterms f1 margs2 in
          
          if not (equal_vars_mterm_list (vars1,margs1') (vars2,margs2'))
          then 
            if vars1 = [] && vars2 = [] 
            then raise NoMatch
            else termAC_eq := (f1,(vars1,margs1'),(vars2,margs2')) :: !termAC_eq
      | _ -> raise NoMatch

    let build_opt f_AC same_remaining_problems remaining_problems = 

      let inside_fun acc f margs1 margs2 = 
        let vars1,margs1' = unfold_rec_and_get_variables_mterms f margs1 in
        let vars2,margs2' = unfold_rec_and_get_variables_mterms f margs2 in
        if equal_vars_mterm_list (vars1,margs1') (vars2,margs2')
        then acc
        else 
          if vars1 = [] && vars2 = []
          then raise NoMatch
          else (f,(vars1,margs1'),(vars2,margs2')) :: acc
      in
      let termAC_eq1 = List.fold_left (fun acc (margs1,margs2) -> inside_fun acc f_AC margs1 margs2) [] same_remaining_problems in
      let termAC_eq2 = List.fold_left (fun acc (f,margs1,margs2) -> inside_fun acc f margs1 margs2) termAC_eq1 remaining_problems in

      try 
        Some 
          {
            term_eq = 
              List.map (fun v -> match v.v_link with
                | FTLink t ->
                    let (vars_t',t') = unfold_rec_and_get_variables_term t in
                    v,(vars_t',t')
                | _ -> failwith "[UnifyMinimal.Constraints] Expecting a link."
              ) !current_bound_vars;
            termAC_eq = termAC_eq2
          }
      with NoMatch -> None

    let create_constraint t1 t2 = 
      let term_eq = ref [] in
      let termAC_eq = ref [] in

      try 
        weak_unify term_eq termAC_eq t1 t2;
        Some { term_eq = !term_eq; termAC_eq = !termAC_eq }
      with NoMatch -> None

    let wedge consl consl' = List.rev_map consl consl'

    let simplify_mterm f ((vars,margs) as vars_mterm) = 
      if List.exists (fun v -> v.v_link <> NoLink) vars
      then unfold_rec_and_get_variables_mterms f margs
      else vars_mterm
    
    let simplify_atomic_constraint modified cons = 
      let term_eq = ref [] in
      let termAC_eq = ref [] in

      try 
        List.iter (fun ((v,(vars2,t2)) as eq) -> match v.v_link with
          | NoLink -> term_eq := eq :: !term_eq
          | FTLink t1 -> modified := true; weak_unify term_eq termAC_eq t1 t2
          | _ -> failwith "[simplify_atomic_constraint] Unexpected link"
        ) cons.term_eq;

        List.iter (fun (f,vars_mt1,vars_mt2) ->
          let (vars1,_) as vars_mt1' = simplify_mterm f vars_mt1 in
          let (vars2,_) as vars_mt2' = simplify_mterm f vars_mt2 in
          if vars_mt1' != vars_mt2'
          then 
            begin
              modified := true;
              if not (equal_vars_mterm_list vars_mt1' vars_mt2')
              then 
                if vars1 = [] && vars2 = []
                then raise NoMatch
                else termAC_eq := (f,vars_mt1',vars_mt2') :: !termAC_eq
            end
        ) cons.termAC_eq;
        
        if !modified
        then Some { term_eq = !term_eq; termAC_eq = !termAC_eq }
        else Some cons
      with NoMatch -> None

    let simplify_constraints consl = 
      let modified = ref false in
      let consl' =
        List.filter_map (fun cons -> match simplify_atomic_constraint modified cons with 
          | Some cons' ->
              if cons'.term_eq = [] && cons'.termAC_eq = []
              then raise NoMatch
              else Some cons'
          | None -> None 
        ) consl
      in
      if !modified then consl' else consl

  end
    
  module ElementaryNew = 
  struct

    open Flattened

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

    let display_vector_nonewline f_print m = 
      for i = 0 to Array.length m - 1 do 
        Printf.printf "%s  " (f_print m.(i))
      done
      
    (* DFS Hullot Tree *)

    type status =
      | NotVisited
      | Visited
      | Finished

    type vertex = 
      {
        mutable status : status;
        successors : (int (* Index *) * int (** Bit representation *)) list
      }

    type occurence_data = 
      {
        vertex_tbl: vertex Array.t;
        roots: int (** Index *) list
      }

    let display_occurrence_data nb_solutions occur_data = 
      Printf.printf "*** Occurrrence data:\n";
      Printf.printf "Roots: %s\n" (string_of_list string_of_int "; " occur_data.roots);
      Printf.printf "Vertex_tbl:\n";
      Array.iteri (fun i vertex ->
        Printf.printf "  %d -> %s\n" i (string_of_list (fun (j,bit_trans) -> Printf.sprintf "(%d,%s)" j (int2bin nb_solutions bit_trans)) " -- " vertex.successors) 
      ) occur_data.vertex_tbl

    exception FoundCycle

    let rec putting_constraints subset_bits (current_constraint_ref:Constraints.t ref) constraints_to_add = match constraints_to_add with
      | [] -> constraints_to_add
      | (cons,bitrepr) as consbit ::q -> 
          let constraints_to_add' = putting_constraints subset_bits current_constraint_ref q in
          if subset_bits land bitrepr = 0
          then 
            begin
              current_constraint_ref := cons :: !current_constraint_ref;
              constraints_to_add'
            end
          else
            if constraints_to_add' == q
            then constraints_to_add
            else consbit :: constraints_to_add'

    let rec filter_constraints subset_bits constraints_to_add = match constraints_to_add with
      | [] -> constraints_to_add
      | (_,bitrepr) as consbit ::q -> 
          let constraints_to_add' = filter_constraints subset_bits q in
          if subset_bits land bitrepr <> 0
          then constraints_to_add'
          else 
            if constraints_to_add' == q
            then constraints_to_add
            else consbit :: constraints_to_add'

    let check_no_cycle occur_data subset_bits =

      let rec dfs idx = 
        let vertex = occur_data.vertex_tbl.(idx) in
        match vertex.status with 
        | Finished -> ()
        | Visited -> raise FoundCycle
        | NotVisited ->
            vertex.status <- Visited;
            List.iter (fun (idx,repr_bits) ->
              if subset_bits land repr_bits <> 0
              then dfs idx
            ) vertex.successors;
            vertex.status <- Finished
      in

      try 
        List.iter dfs occur_data.roots;
        List.iter (fun idx -> occur_data.vertex_tbl.(idx).status <- NotVisited) occur_data.roots;
        true
      with FoundCycle -> 
        List.iter (fun idx -> occur_data.vertex_tbl.(idx).status <- NotVisited) occur_data.roots;
        false

    (** All_bits should also containt the representation of constraints that are not satisfiable *)
    let dfs_hullot_tree f_next (current_constraint:Constraints.t) constraints_to_add true_cons false_cons n all_bits constants_bits occur_data =
      let init_full_one = -1 lsr (Sys.int_size - n) in
    
      let big_enough subset_bits = 
        List.for_all (fun vi -> subset_bits land vi <> 0) all_bits &&
        List.for_all (fun vi -> subset_bits land vi <> 0) false_cons 
      in
      let small_enough subset_bits = 
        List.for_all (fun vi -> (subset_bits land vi) land ((subset_bits land vi) -1) = 0) constants_bits &&
        check_no_cycle occur_data subset_bits &&
        List.for_all (fun vi -> subset_bits land vi = 0) true_cons
      in

      (* When [sign_greater = true], it corresponds to >. *)
      let rec dfs next_dfs current_constraint constaints_to_add pre a k sign_greater = 
        (* Printf.printf "Dfs pre = %s, a = %s, k = %d, sign_greater = %b\n" (int2bin n pre) (int2bin n a) k sign_greater; *)
        let subset_bits, test = 
          if sign_greater 
          then pre lor a, big_enough (pre lor a)
          else pre, small_enough pre 
        in
        if test
        then 
          if k = 0
          then f_next next_dfs current_constraint subset_bits
          else 
            let a' = a lsr 1 in
            if sign_greater
            then 
              let current_constraint_ref = ref current_constraint in
              let constraints_to_add' = putting_constraints subset_bits current_constraint_ref constraints_to_add in
              let current_constraint' = !current_constraint_ref in
              dfs (fun () -> 
                dfs next_dfs current_constraint' constraints_to_add' (pre lor (a lxor a')) a' (k-1) false
              ) current_constraint' constraints_to_add' pre a' (k-1) true
            else
              let constraints_to_add' = filter_constraints subset_bits constraints_to_add in
              dfs (fun () -> 
                dfs next_dfs current_constraint constraints_to_add' (pre lor (a lxor a')) a' (k-1) false
              ) current_constraint constraints_to_add' pre a' (k-1) true
        else next_dfs () 
      in
    
      dfs (fun () -> raise NoMatch) current_constraint constraints_to_add 0 init_full_one n true
    
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
          nb_variables: int;  (** Number of variables in the initial problem *)
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
    
      let display_t store = 
        Array.iteri (fun i elt ->
          if i = Array.length store.elts - 1
          then 
            begin 
              Printf.printf "- Variables :\n";
              List.iter (fun sol ->
                display_vector string_of_int sol;
              ) elt
            end
          else
            begin 
              Printf.printf "- Constant %d:\n" i;
              List.iter (fun sol -> display_vector string_of_int sol) elt
            end
        ) store.elts
        
      let display_t_frozen store = 
        Array.iteri (fun i elt ->
          if i = Array.length store.elts_f - 1
          then 
            begin 
              Printf.printf "- Variables :\n";
              List.iter (fun (sol,defect) ->
                print_string "Sol ";
                display_vector_nonewline (fun (k,b) -> Printf.sprintf "(%d,%b)" k b) sol;
                print_string " with defect ";
                display_vector string_of_int defect;
              ) elt
            end
          else
            begin 
              Printf.printf "- Constant %d:\n" i;
              List.iter (fun (sol,defect) ->
                print_string "Sol ";
                display_vector_nonewline (fun (k,b) -> Printf.sprintf "(%d,%b)" k b) sol;
                print_string " with defect ";
                display_vector string_of_int defect;
              ) elt
            end
        ) store.elts_f
        
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
    
      (* Add the content of store2 in store1 *)
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
          for j = 0 to Array.length storage.elts_t.(i) - 1 do 
            let p' = !p lsl 1 in
            p := if storage.elts_t.(i).(j).(idx) <> 0 then succ p' else p'
          done
        done;
        !p
    
      let generate_bitvector_of_all_constants ground_constants storage =
        let rec loop nb_remaing_solutions idx =
          if idx = storage.nb_constants
          then []
          else
            if ground_constants.(idx) = None
            then
              let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
              let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in
              ((-1 lsr (Sys.int_size - nb_solution_of_constant_idx)) lsl nb_remaing_solutions) :: loop nb_remaing_solutions (idx+1)
            else 
              begin
                (* Printf.printf "Loop nb_remaing_solutions = %d, idx = %d\n" nb_remaing_solutions idx; *)
                let p = ref 0 in
                for i = 0 to storage.nb_constants - 1 do
                  for j = 0 to Array.length storage.elts_t.(i) - 1 do 
                    let p' = !p lsl 1 in
                    p := if storage.elts_t.(i).(j).(idx) <> 0 then succ p' else p'
                  done
                done;
                let full_p = !p lsl Array.length storage.elts_t.(storage.nb_constants) in
                
                let nb_solution_of_constant_idx = Array.length storage.elts_t.(idx) in
                let nb_remaing_solutions = nb_remaing_solutions - nb_solution_of_constant_idx in

                (* Printf.printf "Value p: %s, nb_sol_const_idx: %d, nb_remainig: %d, p_pure_idx: %s, p_full: %s\n" 
                  (int2bin storage.nb_elts_t !p) nb_solution_of_constant_idx nb_remaing_solutions
                  (int2bin storage.nb_elts_t p_pure_idx) (int2bin storage.nb_elts_t full_p)
                  ; *)

                full_p :: loop nb_remaing_solutions (idx+1)
              end
        in
        loop storage.nb_elts_t 0
    
      let generate_bitvectors ground_constants storage = 
        let constant_bitvectors = generate_bitvector_of_all_constants ground_constants storage in
        let all_bitvectors = ref constant_bitvectors in
        for idx = storage.nb_constants to storage.nb_constants + storage.nb_variables - 1 do
          all_bitvectors := generate_bitvectors_of_variable storage idx :: !all_bitvectors
        done;
        constant_bitvectors, !all_bitvectors
    
      (** Generation of the occurrence data *)

      let generate_occurrence_data (occur_variables:(int list *int) Array.t) storage =

        let vertex_tbl = Array.make storage.nb_variables { status = NotVisited; successors = [] } in

        let build_transition_bit idx_xi bit_xj =
          (* if !count_unify = 1
            then 
              begin
                Printf.printf "build_transition_bit (%d,%s)\n" idx_xi (int2bin storage.nb_variables bit_xj);
                flush_all ();
              end; *)
          let p = ref 0 in
          for i = 0 to storage.nb_constants - 1 do
            for j = 0 to Array.length storage.elts_t.(i) - 1 do 
              let p' = !p lsl 1 in
              if storage.elts_t.(i).(j).(idx_xi+storage.nb_constants) <> 0 && bit_xj land (snd occur_variables.(i)) <> 0
              then p := succ p'
              else p := p'
            done
          done;
          !p lsl (Array.length storage.elts_t.(storage.nb_constants))
        in

        let roots = ref [] in

        for i = 0 to storage.nb_variables - 1 do
          let bit_xj = ref (1 lsl (storage.nb_variables - 1)) in
          let succ = ref [] in
          for j = 0 to storage.nb_variables - 1 do
            if i <> j 
            then 
              begin
                let transition_bit = build_transition_bit i !bit_xj in
                if transition_bit <> 0
                then succ := (j,transition_bit) :: !succ
              end;
            bit_xj := !bit_xj lsr 1
          done;
          vertex_tbl.(i) <- { status = NotVisited; successors = !succ };
          if !succ <> [] then roots := i :: !roots
        done;

        { vertex_tbl = vertex_tbl; roots = !roots }

      (** Suitable_bitsubset_to_substitutions *)
      let suitable_bitsubset_to_substitution storage f_AC constants variables ground_constants p = 
        
        (* Reset the recorded term in ground_constants *)
        Array.iter (function None -> () | Some ref_t -> ref_t := dummy) ground_constants;

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
                Array.iteri (fun j ground -> match ground with
                  | None -> ()
                  | Some ref_t ->
                      let k = sol.(j) in
                      if k <> 0
                        then 
                          begin
                            if k <> 1 || !ref_t != dummy then failwith "[Elementary.Storage_solutions] The 'smaller than' test should have discarded this case"; 
                            ref_t := storage.associated_variables.(i)
                          end
                ) ground_constants;
                loop_vars (i - 1) (bit_i lsl 1)
              end
        in

        let rec loop_constants i ith_constant constant sols_constant bit_i =
          (* if !count_unify = 1
          then Printf.printf "loop_constants(%d,%d,%s,%s)\n" i ith_constant (Flattened.string_of_term constant) (int2bin storage.nb_elts_t bit_i); *)
          if i = -1
          then bit_i
          else
            if bit_i land p = 0 (* The subset do not contain the solution *)
            then loop_constants (i - 1) ith_constant constant sols_constant (bit_i lsl 1)
            else 
              begin 
                let sol = sols_constant.(i) in
                (* if !count_unify = 1
                then
                  begin 
                    Printf.printf "Sol: ";
                    display_vector string_of_int sol
                  end; *)

                for j = 0 to Array.length term_links -1 do
                  let k = sol.(j+storage.nb_constants) in
                  if k <> 0
                  then term_links.(j) <- (constant,k) :: term_links.(j)
                done;
                Array.iteri (fun j ground -> match ground with
                  | None -> ()
                  | Some ref_t ->
                    if j != ith_constant
                    then 
                      let k = sol.(j) in
                      if k <> 0
                      then 
                        begin
                          (* if !count_unify = 1
                          then
                            begin 
                              Printf.printf "Recording a term with j: %d\n" j
                            end; *)
                          if k <> 1 || !ref_t != dummy then failwith "[Elementary.Storage_solutions] The 'smaller than' test should have discarded this case"; 
                          ref_t := constant
                        end
                ) ground_constants;
                (bit_i lsl (i + 1))
              end
        in
    
        let rec loop_all_constants ith_constant bit_i = 
          (* Printf.printf "loop_all_constants(%d,%s)\n" ith_constant (int2bin storage.nb_elts_t bit_i); *)
          if ith_constant = - 1
          then ()
          else
            let sols_constant = storage.elts_t.(ith_constant) in
            let bit_i' = loop_constants (Array.length sols_constant - 1) ith_constant constants.(ith_constant) sols_constant bit_i in
            loop_all_constants (ith_constant-1) bit_i'
        in
    
        let bit_i = loop_vars (Array.length storage.associated_variables - 1) 1 in
        loop_all_constants (storage.nb_constants - 1) bit_i;
    
        for i = 0 to Array.length variables - 1 do
          match term_links.(i) with
            | [] -> failwith "[suitable_bitsubset_to_substitution] There should be a term to link."
            (* | [FVar ({v_link = NoLink; } as v),1] -> link v (FTLink (FVar variables.(i))) *)
            | [t,1] -> link variables.(i) (FTLink t)
            | mt -> link variables.(i) (FTLink (FAC(f_AC,mt)))
        done
    
      (** Remove *)
      let remove_equation_from_solutions storage idx_constant local_idx_list_to_remove = 
        (* if !count_unify = 1
          then 
            begin 
              Printf.printf "-- remove_equation_from_solutions(%d,[%s]) with Storage:\n"
                idx_constant (string_of_list string_of_int "," local_idx_list_to_remove);
              display storage;
              flush_all ()
            end; *)

        let elts = Array.map Array.copy storage.elts_t in
        let sol_ar = elts.(idx_constant) in
        let nb_elt_to_remove = List.length local_idx_list_to_remove in
        let new_sol_ar = Array.make (Array.length sol_ar - nb_elt_to_remove) sol_ar.(0) in


        let rec loop i new_i = function
          | [] -> for j = 0 to Array.length sol_ar - 1 - i do new_sol_ar.(new_i+j) <- sol_ar.(i+j) done
          | j::q when i = j -> loop (i+1) new_i q
          | l -> 
              new_sol_ar.(new_i) <- sol_ar.(i); 
              loop (i+1) (new_i+1) l
        in

        loop 0 0 local_idx_list_to_remove;
        elts.(idx_constant) <- new_sol_ar;
        (* if !count_unify = 1
          then 
            begin 
              Printf.printf "Completed remove_equation_from_solutions\n";
              flush_all ()
            end; *)
        { storage with elts_t = elts; nb_elts_t = storage.nb_elts_t - nb_elt_to_remove }
    end
    
    (* In [solve_system_diophantine_equations nb_constants matrix_system], we assume that
      then first [nb_constants] columns of [matrix_system] represents constants. *)
    let solve_system_diophantine_equations nb_constants (occur_variables:(int list * int) Array.t) ground_constants matrix_system =
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
        (* if !count_unify = 1
          then 
            begin
              Printf.printf "*** set_Vk_not_in_Mk:\n";
              Storage_solutions.display_t_frozen set_Vk_not_in_Mk;
              Printf.printf "*** set_Vk_in_Mk:\n";
              Storage_solutions.display_t set_Vk_in_Mk;
              Printf.printf "*** set_rest_Mk:\n";
              Storage_solutions.display_t set_rest_Mk;
              print_string "-------\n"
            end; *)

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
                          (* Froze the previous successful index. *)
                          List.iter (fun l ->
                            new_v.(l) <- (fst new_v.(l), true);
                          ) !success_j;

                          (* If j was a non-ground constant, froze the variables that occur in the constant *)
                          if j < nb_constants && ground_constants.(j) <> None
                          then 
                            begin 
                              if fst new_v.(j) <> 1 then failwith "It should be one";
                              new_v.(j) <- (1, true);
                              List.iter (fun k -> new_v.(k) <- (fst new_v.(k), true)) (fst occur_variables.(j))
                            end;

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
      
      (* Initialise the sets *)
      let e_frozen_template = Array.make nb_variables (0,false) in

      (* Froze all the ground ground constants *)
      for j = 0 to nb_constants - 1 do
        if ground_constants.(j) = None
        then e_frozen_template.(j) <- (0,true)
      done;

      let e_frozen_template_ground = Array.copy e_frozen_template in

      for j = 0 to nb_constants - 1 do 
        if is_null initial_defects.(j)
        then 
          let ej = Array.make nb_variables 0 in
          ej.(j) <- 1;
          Storage_solutions.add init_set_Vk_in_Mk (min j nb_constants) ej;
          if ground_constants.(j) = None
          then
            begin
              e_frozen_template.(j) <- (0,true);
              e_frozen_template_ground.(j) <- (0,true)
            end
          else e_frozen_template.(j) <- (0,true)
        else
          begin
            let ej = 
              if ground_constants.(j) = None
              then 
                begin 
                  let ej' = Array.copy e_frozen_template_ground in
                  e_frozen_template.(j) <- (0,true);
                  e_frozen_template_ground.(j) <- (0,true);
                  ej'
                end
              else
                begin 
                  let ej' = Array.copy e_frozen_template in
                  e_frozen_template.(j) <- (0,true);
                  ej'
                end
            in
            ej.(j) <- (1,true);
            (* Froze the variables that occur in the constant *)
            List.iter (fun k -> ej.(k+nb_constants) <- (0,true)) (fst occur_variables.(j));

            Storage_solutions.add_frozen init_set_Vk_not_in_Mk (min j nb_constants) (ej,initial_defects.(j));
          end
      done;
      
      for j = nb_constants to nb_variables - 1 do 
        if is_null initial_defects.(j)
        then 
          let ej = Array.make nb_variables 0 in
          ej.(j) <- 1;
          Storage_solutions.add init_set_Vk_in_Mk (min j nb_constants) ej
        else
          begin
            let ej = Array.copy e_frozen_template in
            ej.(j) <- (1,false);

            Storage_solutions.add_frozen init_set_Vk_not_in_Mk (min j nb_constants) (ej,initial_defects.(j));
          end;
        e_frozen_template.(j) <- (0,true);
      done;
    
      build_M init_set_Vk_not_in_Mk init_set_Vk_in_Mk;
    
      set_rest_Mk
    
    module MatrixGeneration = struct
    
      let dummy_vars = fresh_variable ()
    
      (* Should be improved when the terms will be DAG *)
      type t = 
        {
          mutable vars: (variable * int Array.t) list;
          mutable nb_vars: int;
          mutable constants: (term * bool (* Is ground when true *) * (int list * int) (* Occur variables *) * int Array.t (* Coeffs *)) list;
          mutable nb_constants: int;
          nb_equations: int
        }

      let display storage = 
        Printf.printf "Storage:\n";
        Printf.printf "  Vars = \n";
        List.iter (fun (v,coeffs) -> Printf.printf "    %s with coeff = " (string_of_variable v); display_vector string_of_int coeffs) storage.vars;
        Printf.printf "  Nb_vars = %d\n" storage.nb_vars;
        Printf.printf "  Constants = \n";
        List.iter (fun (t,ground,occur,coeffs) -> 
          Printf.printf "    %s with ground=%b, occur = ([%s],%s) and coeff = " 
            (string_of_term t)
            ground
            (string_of_list string_of_int "," (fst occur))
            (int2bin storage.nb_vars (snd occur))
        
          ; 
          display_vector string_of_int coeffs
        ) storage.constants;
        Printf.printf "  Nb_constants = %d\n" storage.nb_constants;
        Printf.printf "  Nb_equations = %d\n" storage.nb_equations;
        flush_all ()
    
      let create nb_equations = 
        {
          vars = [];
          nb_vars = 0;
          constants = [];
          nb_constants = 0;
          nb_equations = nb_equations
        }
    
      let add_variable store ith_eq v k = 
        let rec loop list_variables = match list_variables with
          | [] -> 
              (* The variable is greater than all *)
              let coeffs = Array.make store.nb_equations 0 in
              coeffs.(ith_eq) <- k;
              store.nb_vars <- store.nb_vars + 1;
              [v,coeffs]
          | ((v',coeffs') as v_coeff)::q_vars ->
              match compare_variable v v' with
              | 0 -> 
                  coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
                  list_variables
              | -1 -> 
                  (* The variable was not recorded *)
                  let coeffs = Array.make store.nb_equations 0 in
                  coeffs.(ith_eq) <- k;
                  store.nb_vars <- store.nb_vars + 1;
                  (v,coeffs) :: list_variables
              | _ -> v_coeff :: loop q_vars
        in
        store.vars <- loop store.vars
    
      let add_constant store t is_ground occur_vars ith_eq k = 
        let rec loop list_constants = match list_constants with
          | [] -> 
              (* The constant is greater than all *)
              let coeffs = Array.make store.nb_equations 0 in
              coeffs.(ith_eq) <- k;
              store.nb_constants <- store.nb_constants + 1;
              [t,is_ground,occur_vars,coeffs]
          | ((t',_,_,coeffs') as t_coeff)::q_const ->
              match compare t t' with
              | 0 -> 
                  coeffs'.(ith_eq) <- coeffs'.(ith_eq) + k;
                  list_constants
              | -1 -> 
                  (* The variable was not recorded *)
                  let coeffs = Array.make store.nb_equations 0 in
                  coeffs.(ith_eq) <- k;
                  store.nb_constants <- store.nb_constants + 1;
                  (t,is_ground,occur_vars,coeffs) :: list_constants
              | _ -> t_coeff :: loop q_const
        in
        store.constants <- loop store.constants
    
      type link+= ILink of int

      let filter_index_bool bool_ar = 
        let p = ref 0 in
        let rec loop acc i_repr = function
          | -1 -> acc, !p
          | i -> 
              if bool_ar.(i)
              then 
                begin 
                  p := !p lor i_repr; 
                  loop (i::acc) (i_repr lsl 1) (i-1)
                end
              else loop acc (i_repr lsl 1) (i-1)
        in
        loop [] 1 (Array.length bool_ar - 1)

      let unfold_term_with_occur_vars nb_variables t =
        let ground = ref true in
        let occur_variables = Array.make nb_variables false in

        let rec loop t = match t with
          | FVar { v_link = FTLink t; _ } -> loop t
          | FVar { v_link = ILink j; _ } ->
              occur_variables.(j) <- true;
              ground := false;
              t
          | FVar _ -> ground := false; t
          | FFunc(f,args) -> 
              let args' = List.mapq loop args in
              if args == args' then t else FFunc(f,args')
          | FAC(f,margs) -> 
              let margs' = 
                List.mapq (fun ((t,k) as pair)-> 
                  let t' = loop t in
                  if t == t' then pair else (t',k)
                ) margs
              in
              if margs' == margs then t else FAC(f,margs') 
        in

        let t_unfolded = loop t in
        !ground, filter_index_bool occur_variables, t_unfolded

      let get_occur_vars nb_variables t = 
        let occur_variables = Array.make nb_variables false in

        let rec loop t = match t with
          | FVar { v_link = FTLink t; _ } -> loop t
          | FVar { v_link = ILink j; _ } ->
              occur_variables.(j) <- true
          | FVar _ -> ()
          | FFunc(_,args) -> List.iter loop args
          | FAC(_,margs) -> List.iter (fun (t,_) -> loop t) margs 
        in

        loop t;
        filter_index_bool occur_variables

      let cleanup_variables store = 
        let rec loop = function 
          | [] -> []
          | (_,coeffs) as v_data ::q ->
              if Array.for_all (fun i -> i = 0) coeffs
              then 
                begin 
                  store.nb_vars <- store.nb_vars - 1;
                  loop q
                end
              else v_data :: loop q
        in
        store.vars <- loop store.vars

      let cleanup_constants store = 
        let rec loop = function 
          | [] -> []
          | ((_,_,_,coeffs) as t_data) ::q ->
              if Array.for_all (fun i -> i = 0) coeffs
              then 
                begin 
                  store.nb_constants <- store.nb_constants - 1;
                  loop q
                end
              else t_data :: loop q
        in
        store.constants <- loop store.constants

      let cleanup_equations matrix = 
        let empty_equations = ref [] in
        let count_empty_eq = ref 0 in

        for i = 0 to Array.length matrix - 1 do
          if Array.for_all (fun k -> k = 0) matrix.(i)
          then (empty_equations := i :: !empty_equations; incr count_empty_eq)
        done;

        if !empty_equations <> []
        then 
          let new_matrix = Array.make (Array.length matrix - !count_empty_eq) matrix.(0) in
          let rec loop i new_i = function 
            | [] -> for j = 0 to Array.length matrix - 1 - i do new_matrix.(new_i+j) <- matrix.(i+j) done
            | j::q when i = j -> loop (i+1) new_i q
            | l -> 
                new_matrix.(new_i) <- matrix.(i); 
                loop (i+1) (new_i+1) l
          in
          loop 0 0 (List.rev !empty_equations);
          new_matrix
        else matrix

      let from_unification_equations f_AC system_equations = 
        if system_equations = []
        then failwith "[Flattened.Elementary.MatrixGeneration.from_matching_equations] The system of equations should not be empty";

        let nb_equations = List.length system_equations in
        let store = create nb_equations in

        (* Unfold variables and F_AC *)
        let system_equations = 
          List.map (fun (left_l,right_l) ->
            let new_left_l = ref [] in
            let new_right_l = ref [] in 
            List.iter (unfold_AC_only f_AC new_left_l) left_l;
            List.iter (unfold_AC_only f_AC new_right_l) right_l;
            !new_left_l,!new_right_l
          ) system_equations
        in

        (* if !count_unify = 1
        then 
          begin
            Printf.printf "from_unification_equations: After unfolding\n";
            List.iter (fun (mtl1,mtl2) ->
              Printf.printf "  %s = %s\n"
                (string_of_list (fun (t,k) -> Printf.sprintf "(%s,%d)" (string_of_term t) k) ", " mtl1)
                (string_of_list (fun (t,k) -> Printf.sprintf "(%s,%d)" (string_of_term t) k) ", " mtl2)
            ) system_equations
          end; *)

        let non_variable_terms = ref [] in

        (* Unfold variable link and f_AC *)

        (* Add only variables *)
        List.iteri (fun i (left_eq,right_eq) ->
          List.iter (function (t,k) -> match t with
            | FVar v -> add_variable store i v k
            | t -> non_variable_terms := (i,t,k) :: !non_variable_terms
          ) left_eq;
          List.iter (function (t,k) -> match t with
            | FVar v -> add_variable store i v (-k)
            | t -> non_variable_terms := (i,t,-k) :: !non_variable_terms
          ) right_eq;
        ) system_equations;

        cleanup_variables store;

        auto_cleanup_no_catch (fun () ->
          (* Link the variables *)
          List.iteri (fun i (v,_) -> link v (ILink i)) store.vars;

          let nb_variables = store.nb_vars in
            
          (* Add terms *)
          List.iter (fun (ith_eq,t,k) ->
            let (is_ground,occur_vars,t_unfolded) = unfold_term_with_occur_vars nb_variables t in
            add_constant store t_unfolded is_ground occur_vars ith_eq k
          ) !non_variable_terms;

          cleanup_constants store
        );

        let matrix = Array.make_matrix store.nb_equations (store.nb_constants + store.nb_vars) 0 in
        let variables = Array.make store.nb_vars dummy_vars in
        let constants = Array.make store.nb_constants dummy in
        let occur_variables = Array.make store.nb_constants ([],0) in
        let ground_constants = Array.make store.nb_constants None in

        (* Register the variables *)
        List.iteri (fun j (v,coeffs) ->
          variables.(j) <- v;
          Array.iteri (fun i k ->
            matrix.(i).(store.nb_constants+j) <- k
          ) coeffs  
        ) store.vars;

        (* Register the constants *)
        List.iteri (fun j (t,is_ground,occur_vars,coeffs) ->
          constants.(j) <- t;
          occur_variables.(j) <- occur_vars;
          if not is_ground then ground_constants.(j) <- Some (ref dummy);
          Array.iteri (fun i k ->
            matrix.(i).(j) <- k
          ) coeffs  
        ) store.constants;

        (cleanup_equations matrix,variables,store.nb_vars,constants,store.nb_constants,occur_variables,ground_constants)

    end 
     
    (** Retrieving from the solutions the equations between terms and transform them in constraints *)

    let create_constraints_from_solutions constants ground_status solutions =

      let last_idx_constant = Array.length constants - 1 in

      (* search_in_constraint_space *) 
      
      let bit_repr_fst_sol_idx_contant1 = ref (1 lsl (solutions.Storage_solutions.nb_elts_t - 1)) in
      let accumulator_constraints = ref [] in

      let exploration_one_equation idx_constant1 idx_constant2 = 
        let bit_repr_col = ref !bit_repr_fst_sol_idx_contant1 in
        let bit_repr_eq = ref 0 in

        (* We now explore the solution *)
        for i = 0 to Array.length solutions.elts_t.(idx_constant1) - 1 do
          if solutions.elts_t.(idx_constant1).(i).(idx_constant2) = 1
          then bit_repr_eq := !bit_repr_col lor !bit_repr_eq;
          bit_repr_col := !bit_repr_col lsr 1
        done;

        if !bit_repr_eq <> 0
        then accumulator_constraints := (idx_constant1,idx_constant2,!bit_repr_eq) :: !accumulator_constraints
      in

      for idx_constant1 = 0 to last_idx_constant do 
        if ground_status.(idx_constant1) = None
        then
          (* The constrant is ground thus we only need to look at the column of non-ground constant *)
          for idx_constant2 = 0 to last_idx_constant do 
            if ground_status.(idx_constant2) <> None
            then exploration_one_equation idx_constant1 idx_constant2
          done
        else
          (* The constrant is not ground thus we need to look at all column after idx_constant1  *)
          for idx_constant2 = idx_constant1 + 1 to last_idx_constant do 
            exploration_one_equation idx_constant1 idx_constant2
          done;
        
        bit_repr_fst_sol_idx_contant1 := !bit_repr_fst_sol_idx_contant1 lsr (Array.length solutions.elts_t.(idx_constant1))
      done;

      (* We now need to create the constraint per say *)
      let false_constraints = ref [] in
      let true_constraints = ref [] in
      let constraints_to_add = ref [] in 

      List.iter (fun (idx1,idx2,bitrepr) ->
        match Constraints.create_constraint constants.(idx1) constants.(idx2) with
        | None -> 
            (* The constraint is always true *)
            true_constraints := bitrepr :: !true_constraints;
        | Some cons ->
            if Constraints.is_false cons
            then false_constraints := bitrepr :: !false_constraints
            else constraints_to_add := (cons,bitrepr) :: !constraints_to_add 
      ) !accumulator_constraints;

      (!constraints_to_add,!false_constraints,!true_constraints)

    let solve f_next neg_constraint_list remaining_problems f_AC matrix_system variables nb_variables constants nb_constants occur_variables ground_constant_status =
      if !count_unify = 1
      then 
        begin 
          print_string "Matrix =\n";
          display_matrix string_of_int matrix_system;
          Printf.printf "Variables (%d) = " nb_variables;
          display_vector string_of_variable variables;
          Printf.printf "Constants (%d) = " nb_constants;
          display_vector string_of_term constants;
          Printf.printf "Occur_variables = ";
          display_vector (fun (l,bit) -> Printf.sprintf "([%s],%s)" (string_of_list string_of_int ";" l) (int2bin nb_variables bit)) occur_variables;
          Printf.printf "Ground constants = ";
          display_vector (function None -> "true" | _ -> "false") ground_constant_status;
          flush_all ();
        end;
      
      if nb_variables = 0 && nb_constants = 0 
      then 
        (* The system is trivially true *)
        f_next neg_constraint_list remaining_problems
      else
        begin 
          (* Solving the matrix system *)
          let solutions = solve_system_diophantine_equations nb_constants occur_variables ground_constant_status matrix_system in
          let nb_solutions = solutions.Storage_solutions.nb_elts in
          
          if nb_solutions > Sys.int_size - 2
          then failwith "Limit on the number of solutions reached";
        
          if nb_solutions = 0 then raise NoMatch;
        
          let finalized_solutions = Storage_solutions.finalize nb_constants nb_variables solutions in

          if !count_unify = 1
          then 
            begin
              Printf.printf "** Finalized solutions\n";
              Storage_solutions.display finalized_solutions
            end;
        
          (* Create the constraints to add and the bit represention of the ones that are always true/false. *)
          let constraints_to_add,false_constraints,true_constraints = create_constraints_from_solutions constants ground_constant_status finalized_solutions in

          (* Bit presentation to subset of solutions *)
          let (constant_bitvectors,all_bitvectors) = Storage_solutions.generate_bitvectors ground_constant_status finalized_solutions in
          let occurence_data = Storage_solutions.generate_occurrence_data occur_variables finalized_solutions in

          if !count_unify = 1
          then 
            begin 
              Printf.printf "\n** Constant bitvectors\n";
              List.iter (fun p ->
                Printf.printf "bit = %s\n" (int2bin nb_solutions p)
              ) constant_bitvectors;
              Printf.printf "\n** All bitvectors\n";
              List.iter (fun p ->
                Printf.printf "bit = %s\n" (int2bin nb_solutions p)
              ) all_bitvectors;
              display_occurrence_data finalized_solutions.nb_elts_t occurence_data;
              Printf.printf "** Constraints:\n";
              Printf.printf "  Constraint to add: %s\n" (string_of_list (fun (cons,bit) -> Printf.sprintf "{%s}%s" (int2bin nb_solutions bit) (Constraints.string_of_atomic cons)) " && " constraints_to_add);
              Printf.printf "  False constraints: %s\n" (string_of_list (int2bin nb_solutions) ", " false_constraints);
              Printf.printf "  True constraints: %s\n" (string_of_list (int2bin nb_solutions) ", " true_constraints);
              flush_all ();
            end;

            dfs_hullot_tree (fun f_next_dfs neg_constraint_list' p ->
              try 
                auto_cleanup_noreset (fun () ->
                  if !count_unify = 1
                  then 
                    begin
                      Printf.printf "Building the substitution %d with %s\n\n\n" !count_subst (int2bin nb_solutions p);
                      flush_all ()
                    end;
                  Storage_solutions.suitable_bitsubset_to_substitution finalized_solutions f_AC constants variables ground_constant_status p;
                  
                  f_next neg_constraint_list' remaining_problems
                )
              with NoMatch -> f_next_dfs ()
            ) neg_constraint_list constraints_to_add true_constraints false_constraints nb_solutions all_bitvectors constant_bitvectors occurence_data
          
        end

    let unification f_next neg_constraint_list remaining_problems f_AC system_equations = 
      let (matrix_system,variables,nb_variables,constants,nb_constants,occur_variables,ground_constants) = MatrixGeneration.from_unification_equations f_AC system_equations in
      
      solve (fun neg_constraint_list' remaining_problems' ->
        let new_equations = ref [] in

        for i = 0 to nb_constants - 1 do
          match ground_constants.(i) with
          | None -> ()
          | Some ref_t ->
              if !ref_t != dummy then new_equations := (constants.(i),!ref_t) :: !new_equations
        done;

        f_next neg_constraint_list' remaining_problems' !new_equations
      ) neg_constraint_list remaining_problems f_AC matrix_system variables nb_variables constants nb_constants occur_variables ground_constants
      
  end

  let rec flatten_term f mlist t k = match t with
    | FVar { v_link = FTLink ((FVar _) as t') } -> flatten_term f mlist t' k
    | FVar { v_link = FTLink (FAC(f',margs')); _ } when f == f' ->
        List.fold_left (fun acc_mlist (t',k') ->
          flatten_term f acc_mlist t' (k*k')
        ) mlist margs'
    | FVar { v_link = FTLink t'; _ } -> add_multiplicity f t' k mlist
    | FAC(f',margs') when f == f' -> 
        List.fold_left (fun acc_mlist (t',k') ->
          flatten_term f acc_mlist t' (k*k')
        ) mlist margs'
    | _ -> add_multiplicity f t k mlist

  let flatten_mterm_list f mlist = 
    List.fold_left (fun acc_mlist (t,k) ->
      flatten_term f acc_mlist t k
    ) [] mlist

  let rec partition_remaining_problems f_target = function
    | [] -> [], []
    | (f,mlist1,mlist2) :: q when f == f_target ->
        let same_f_problems, other_problems = partition_remaining_problems f_target q in
        (flatten_mterm_list f_target mlist1,flatten_mterm_list f_target mlist2)::same_f_problems, other_problems
    | pbl::q -> 
        let same_f_problems, other_problems = partition_remaining_problems f_target q in
        same_f_problems, pbl::other_problems

  let rec solve_remaining_problems f_next neg_constraint_list remaining_problems = match remaining_problems with
    | [] -> 
        if !count_unify = 1 then Printf.printf "*** Final constraints: %s\n" (Constraints.string_of_constraints neg_constraint_list);
        let _ = Constraints.simplify_constraints neg_constraint_list in 
        f_next ()
    | (f,_,_) :: _ ->
        let same_f_problems, other_problems = partition_remaining_problems f remaining_problems in
        if same_f_problems = [] then failwith "[Unify.solve_remaining_problems] There should be at least one problem corresponding to the function symbol.";
        ElementaryNew.unification (fun neg_constraint_list' remaining_problems' new_equations ->
          if !count_unify = 1
          then 
            begin
              Printf.printf "After ElementaryNew.unification \n";
              let subst = 
                List.fold_left (fun acc v -> match v.v_link with 
                  | FTLink t -> (v,Flattened.copy_term_rec t)::acc
                  | NoLink -> acc
                  | _ -> failwith "[matching_one] Unexpected case"
                ) [] !current_bound_vars
              in
              Printf.printf "Current subst = %s\n" (string_of_subst subst);
              Printf.printf "New equations : %s\n" (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " new_equations);
              flush_all ();
            end;
          auto_cleanup_noreset (fun () ->
            let remain_ref = ref remaining_problems' in
            List.iter (fun (t1,t2) -> unify_term_aux remain_ref t1 t2) new_equations;
            solve_remaining_problems f_next (Constraints.simplify_constraints neg_constraint_list') !remain_ref  
          )
        ) neg_constraint_list other_problems f same_f_problems

  let unify f_next eq_list = 
    incr count_unify;
    if !count_unify = 1
      then 
        begin
          Printf.printf "Unification %d of %s\n"
            !count_unify 
            (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
          flush_all ();
        end;
    let vars = get_variables_in_equations eq_list in
    auto_cleanup (fun () ->
      let remain_ref = ref [] in
      List.iter (fun (t1,t2) ->
        unify_term_aux remain_ref t1 t2
      ) eq_list;
      solve_remaining_problems (fun () ->
        let subst = 
          List.fold_left (fun acc v -> match v.v_link with 
            | FTLink t -> (v,Flattened.copy_term_rec t)::acc
            | NoLink -> acc
            | _ -> failwith "[matching_one] Unexpected case"
          ) [] vars
        in
        f_next subst
      ) [] !remain_ref
    )

  let verify_unifier eq_list subst =
    if not (List.for_all (fun (t1,t2) ->
        let t1' = apply_subst subst t1 in
        let t2' = apply_subst subst t2 in
        equal t1' t2'
      ) eq_list)
    then
      begin
        begin 
          Printf.printf "*** Problem %d: Found a wrong unifier %s\n"
            !count_unify
              (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
          Printf.printf "- Subst = %s\n" (string_of_subst subst);
          failwith "Error"
        end
      end

  (* Does there exists \theta such that x subst2 =AC x subst1\theta for all variables x of the problems *)
  let subst_implies vars subst1 subst2 =
    let list1 = List.map (fun v -> apply_subst subst1 (FVar v)) vars in
    let list2 = List.map (fun v -> apply_subst subst2 (FVar v)) vars in

    find_matching_term_list list1 list2

  let is_subst_implies vars subst1 subst2 =
    let list1 = List.map (fun v -> apply_subst subst1 (FVar v)) vars in
    let list2 = List.map (fun v -> apply_subst subst2 (FVar v)) vars in

    None <> find_matching_term_list list1 list2

  let verify_minimality str eq_list subst_list =
    let header_printed = ref false in
    let vars = get_variables_in_equations eq_list in

    let rec loop visited_subst = function 
      | [] -> visited_subst
      | subst :: q_subst ->
          if List.exists (fun subst' -> is_subst_implies vars subst' subst) visited_subst
          then loop visited_subst q_subst
          else loop (subst :: (List.filter_rev (fun subst' -> not (is_subst_implies vars subst subst')) visited_subst)) q_subst
    in
    let minmal_set = loop [] subst_list in
    let minimal_set_size = List.length minmal_set in
    let set_size = List.length subst_list in

    if minimal_set_size <> set_size
    then 
      begin 
        header_printed := true;
        Printf.printf "*** Unification %d (%s) not minimal in %s\n"
          !count_unify str
          (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
        Printf.printf "  Number of substitutions in original set: %d\n" set_size;
        Printf.printf "  Number of substitutions in minimal set: %d\n" minimal_set_size;
        Printf.printf "  Gain: %d\n" (set_size - minimal_set_size);
        Printf.printf "  Original set:\n";
        List.iteri (fun i subst -> Printf.printf "   Subst %d = %s\n" i (string_of_subst subst)) subst_list;
        Printf.printf "  Minimal set:\n";
        List.iteri (fun i subst -> Printf.printf "   Subst %d = %s\n" i (string_of_subst subst)) minmal_set;
      end
    
  let verify_correctness eq_list subst_maude_l subst_native_l = 
    let vars = get_variables_in_equations eq_list in
    let header_printed = ref false in
    let correct = ref true in

    let display (i2,subst2) =
      if not !header_printed
        then 
          begin 
            header_printed := true;
            Printf.printf "*** Unification %d incorrect in %s\n"
              !count_unify 
              (string_of_list (fun (t1,t2) -> Printf.sprintf "%s = %s" (string_of_term t1) (string_of_term t2)) " && " eq_list);
          end;
        Printf.printf "- Subst_%d = %s\n" i2 (string_of_subst subst2)
    in

    let rec loop i = function 
      | [] -> ()
      | subst :: q_subst ->
          if 
            List.for_all (fun subst_native ->
              match subst_implies vars subst_native subst with 
              | None -> true
              | _ -> false
            ) subst_native_l
          then 
            begin 
              display (i,subst);
              correct := false
            end;
          loop (i+1) q_subst
    in

    loop 1 subst_maude_l;
    !correct

end
  
(***************
   Unification 
****************)

(* Print to maude *)

let maude_string_of_variable v =
  Maude_function.record_old_variable v;
  Printf.sprintf "X%d:Bitstring" v.v_id

let rec maude_string_of_term = function
  | Var v -> maude_string_of_variable v
  | Func(f,[]) -> f.f_name
  | Func(f,args) -> Printf.sprintf "%s(%s)" f.f_name (string_of_list maude_string_of_term "," args)

let maude_get_unifiers maude_out =
  let lexbuf = (Lexing.from_channel maude_out) in
  Maude_parser.unification Maude_lexer.token lexbuf

let maude_make_unifier_query eq_list maude_in =
  let maude_eq_list = 
    string_of_list (fun (s,t) ->
      Printf.sprintf "%s =? %s" (maude_string_of_term s) (maude_string_of_term t)
    ) " /\ " eq_list
  in
  (* Printf.printf "unify %s .\n" maude_eq_list; *)
  Printf.fprintf maude_in "unify %s .\n" maude_eq_list

let rec unflatten = function
  | Var _ as t -> t
  | Func(f,args) when f.f_cat = Syntactic -> Func(f,List.map unflatten args)
  | Func(f,args) -> unflatten_list f args

and unflatten_list f = function
  | [] | [_] -> failwith "Error format"
  | [t1;t2] -> Func(f,[unflatten t1;unflatten t2])
  | t1::l -> Func(f,[unflatten t1;unflatten_list f l])

let unify eq_list =
  Maude_function.run_maude (maude_make_unifier_query eq_list) (fun chan -> 
    try 
      let continue = ref true in
      while !continue do 
        let line = input_line chan in 
        if line = "X:FakeType --> X:FakeType" 
        then continue := false;
        (* print_string line; *)
        (* print_newline () *)
      done
    with End_of_file -> close_in chan
  );

  let result = 
    Maude_function.run_maude (maude_make_unifier_query eq_list) (fun chan -> maude_get_unifiers chan)
  in
  Hashtbl.clear Maude_function.old_variable_table;
  Hashtbl.clear Maude_function.fresh_variable_table;
  List.map (fun subst -> List.map (fun (x,t) -> (x,unflatten t)) subst) result

let unify term1 term2 = 
  let res_maude = unify [term1,term2] in
  res_maude

(*************************
   Unification modulo AC 
**************************)

(* 
let _ = 
  let plus = { f_name = "+"; f_id= 4; f_cat = AC; f_arity = 2 } in
  let a = Flattened.FFunc({ f_name = "a"; f_id= 0; f_cat = Syntactic; f_arity = 0 },[]) in
  let b = Flattened.FFunc({ f_name = "b"; f_id= 1; f_cat = Syntactic; f_arity = 0 },[]) in
  let c = Flattened.FFunc({ f_name = "c"; f_id= 2; f_cat = Syntactic; f_arity = 0 },[]) in
  let d = Flattened.FFunc({ f_name = "d"; f_id= 3; f_cat = Syntactic; f_arity = 0 },[]) in
  let x1 = Flattened.FVar (fresh_variable ()) in
  let x2 = Flattened.FVar (fresh_variable ()) in
  let x3 = Flattened.FVar (fresh_variable ()) in
  let x4 = Flattened.FVar (fresh_variable ()) in
  let x5 = Flattened.FVar (fresh_variable ()) in

  let count = ref 1 in
  let display_subst () = 
    Printf.printf "subst %d = { " !count;
    incr count;
    List.iter (fun v -> match v.v_link with
      | Flattened.FTLink t -> Printf.printf "%s -> %s, " (string_of_variable v) (Flattened.string_of_term t)
      | _ -> failwith "Error"
    ) !current_bound_vars;
    print_string "}\n";
    raise Flattened.NoMatch
  in
  let system_equations = 
    [
      [ (x1,1); (x2,1) ], [ (a,2); (b,2) ]
    ]
  in
  matching_elementary display_subst plus system_equations;
  let system_equations = 
    [
      [ (x1,1) ], [ (a,2); (b,2) ]
    ]
  in
  matching_elementary display_subst plus system_equations;

  count := 0;
  let system_equations = 
    [
      [ (x1,3) ], [ (x2,1); (x3,1); (x4,1); (x5,1) ]
    ]
  in

  unification_elementary (fun () -> incr count; raise Flattened.NoMatch) plus system_equations;
  Printf.printf "Number of unifier: %d\n" !count *)