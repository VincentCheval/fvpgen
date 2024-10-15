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

open AC
open Flattened
open Term

type order_type = 
  | ACRPO
  | CountSymbol

let order_chosen = ref ACRPO

let fixed_order = ref false

(** Compare symbol **)

type link += FMultiplicity of int * int

exception Multiplicity_Not_Included

let rec greater_compute_count k = function
  | Flattened.FVar v ->
      begin match v.v_link with 
      | NoLink -> link v (FMultiplicity (0,k))
      | FMultiplicity (0,j) -> v.v_link <- FMultiplicity (0,j+k)
      | _ -> failwith "[left_compute_count] Unexpected links"
      end;
      1
  | Flattened.FFunc(_,args) -> List.fold_left (fun count t -> count + (greater_compute_count k) t) 1 args
  | Flattened.FAC(f,args) -> List.fold_left (fun count (t,k') -> count + (greater_compute_count (k*k') t)*k' + k' ) (-1) args

(* We assume that the count has been done for the term that should be equal *)
let rec lesser_compute_count k = function
  | Flattened.FVar v ->
      begin match v.v_link with 
      | NoLink -> raise Multiplicity_Not_Included
      | FMultiplicity (i,j) -> 
          if i+k > j then raise Multiplicity_Not_Included;
          v.v_link <- FMultiplicity (i+k,j)
      | _ -> failwith "[left_compute_count] Unexpected links"
      end;
      1
  | Flattened.FFunc(_,args) -> List.fold_left (fun count t -> count + (lesser_compute_count k) t) 1 args
  | Flattened.FAC(f,args) -> List.fold_left (fun count (t,k') -> count + (lesser_compute_count (k*k') t)*k' + k' ) (-1) args

let compare_count_symbol s t = 
  let initial_result =
    try 
      let nb_symb_t, nb_symb_s = 
        auto_cleanup (fun () ->
          let nb1 = greater_compute_count 1 t in
          let nb2 = lesser_compute_count 1 s in
          nb1,nb2
        )
      in
      if nb_symb_t > nb_symb_s
      then Less
      else if nb_symb_t = nb_symb_s 
      then Eq
      else Unknown  
    with Multiplicity_Not_Included -> Unknown
  in

  match initial_result with
  | Eq -> Flattened.compare_strong s t
  | _ -> initial_result 

(** All compare **)

let compare_strong s t = match !order_chosen with
  | ACRPO -> Flattened.compare_strong s t
  | CountSymbol -> compare_count_symbol s t