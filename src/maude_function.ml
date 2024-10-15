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

let channel_tmp = open_out "/tmp/fvp.input"

let old_variable_table : (int,variable) Hashtbl.t = Hashtbl.create 1

let record_old_variable v =
  if not (Hashtbl.mem old_variable_table v.v_id) then Hashtbl.add old_variable_table v.v_id v

let get_old_variable n =
  Hashtbl.find old_variable_table n

let fresh_variable_table : (int,variable) Hashtbl.t = Hashtbl.create 1

let get_fresh_variable n =
	try
    Hashtbl.find fresh_variable_table n
  with Not_found ->
		let v = fresh_variable () in
		Hashtbl.add fresh_variable_table n v;
		v

let cleanup_fresh_variable () = Hashtbl.clear fresh_variable_table

let rec dupplicate_string str n = 
  if n = 0
  then []
  else str :: dupplicate_string str (n-1) 

let maude_out,maude_in = Unix.open_process "maude -batch -no-banner -no-ansi-color -no-advise"

let print_module maude_in = 
  Printf.fprintf maude_in "fmod TH is\n";
  Printf.fprintf maude_in "  sort Bitstring .\n";
  Printf.fprintf maude_in "  sort FakeType .\n";
  List.iter (fun f ->
    Printf.fprintf maude_in "  op %s : %s -> Bitstring [ctor%s] .\n"
      f.f_name (* Name *)
      (string_of_list (fun s -> s) " " (dupplicate_string "Bitstring" f.f_arity)) (* Argument Type *)
      (if f.f_cat = Syntactic then "" else " assoc comm")
  ) !Term.all_symbols;
  Printf.fprintf maude_in "endfm\n\n"

let record_maude_query print_query = 
  print_query channel_tmp

let run_maude print_query parse_result =
  print_module maude_in;
  print_query maude_in;
  (* print_query stdout; *)
  Printf.fprintf maude_in "match X:FakeType <=? X:FakeType .\n";
  flush_all ();
  parse_result maude_out