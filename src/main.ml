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
open Term
open Rewrite_rule
open Input_function

open Lexing
exception InputError of string * (Lexing.position * Lexing.position)


let get_extent v (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    None
  else
    Some (
    let ch_start = loc_start.pos_cnum - loc_start.pos_bol + 1 in
    let ch_end = loc_end.pos_cnum - loc_end.pos_bol in
    if (not v) then
      if ch_start >= ch_end then
	"Character " ^ (string_of_int ch_start)
      else 
        "Characters " ^ (string_of_int ch_start)
         ^ "-" ^ (string_of_int ch_end)
    else
       "File \"" ^ loc_start.pos_fname ^ "\", " ^
       (if loc_start.pos_lnum = loc_end.pos_lnum then
          if ch_start >= ch_end then
            "line " ^ (string_of_int loc_start.pos_lnum)
            ^ ", character " ^ (string_of_int ch_start)
          else
            "line " ^ (string_of_int loc_start.pos_lnum)
            ^ ", characters " ^ (string_of_int ch_start)
            ^ "-" ^ (string_of_int ch_end) 
        else
          "line " ^ (string_of_int loc_start.pos_lnum)
          ^ ", character " ^ (string_of_int ch_start)
          ^ " - line " ^ (string_of_int loc_end.pos_lnum)
          ^ ", character " ^ (string_of_int ch_end)))

let get_extent_string v ext =
  match get_extent v ext with
  | None -> ""
  | Some s -> s ^":\n"
      
  let add_point_if_necessary mess =
    if (String.length mess > 0) &&
      (let end_char = String.get mess (String.length mess - 1) in
      end_char != '.' && end_char != '?' && end_char != '!')
    then
      "."
  else
      ""

(* Get the message to write from mess and ext. Verbose if v is true *)
let get_mess_from v prefix mess ext =
  (get_extent_string v ext) ^ prefix ^  mess ^ add_point_if_necessary mess

(* Print the message with the location of the error, and a point at the end if needed. *)
let display_input_error mess ext =
  print_endline (get_mess_from true "Error: " mess ext);
  exit 2

let parse_file filename = 
  try
    let ic = open_in filename in
    let lexbuf = Lexing.from_channel ic in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
                                  Lexing.pos_fname = filename };
    let (decl_list,rwsysRn_op,eqE) =
      try
        Input_parser.all Input_lexer.token lexbuf
      with Parsing.Parse_error ->
        failwith "Syntax error"
    in
    close_in ic;
    Input_function.parse_declarations decl_list rwsysRn_op eqE
  with Sys_error s ->
    failwith ("File error: " ^ s)

let only_load = ref false

let analyze_file filename =
  let (rwsysRn_op,rw_rules) = parse_file filename in
  
  Printf.printf "file parsed...\n";
  Printf.printf "---Input equation\n";
  display_list (fun () -> print_string "  Empty") (fun rw -> Printf.printf "  %s\n" (string_of_equation rw)) "" rw_rules;
  flush_all ();
  print_string "\n";
  Maude_function.print_module Maude_function.channel_tmp;
  let ((rwsysR,rwsysRn,eqEn),conv_op,nb_rules_computed) = generate_extended_signature rwsysRn_op rw_rules in
  Printf.printf "---Extended signature\n";
  Printf.printf "Rewrite system R:\n";
  display_list (fun () -> print_string "  Empty\n") (fun rw -> Printf.printf "  %s\n" (string_of_rewrite_rule rw)) "" rwsysR;
  Printf.printf "Rewrite system Rn:\n";
  display_list (fun () -> print_string "  Empty\n") (fun rw -> Printf.printf "  %s\n" (string_of_rewrite_rule rw)) "" rwsysRn;
  Printf.printf "Equations En\n";
  display_list (fun () -> print_string "  Empty\n") (fun rw -> Printf.printf "  %s\n" (string_of_equation rw)) "" eqEn;
  Printf.printf "\n";
  flush_all ();
  begin match conv_op with
  | None -> Printf.printf "We could not show that the extended signature was shown to induce a En-convergent rewrite system for E\n"
  | Some rwsys ->
      Printf.printf "The following rewrite system is En-convergent for E\n";
      display_list (fun () -> print_string "  Empty\n") (fun rw -> Printf.printf "  %s\n" (string_of_rewrite_rule rw)) "" rwsys
  end;
  Printf.printf "\nNumber of rules computed: %d\n" nb_rules_computed;
  ignore (Unix.close_process (Maude_function.maude_out,Maude_function.maude_in))

let _ =
  Arg.parse
  [ "-vl", Arg.Set Rewrite_rule.verbose_loop, "Display rewrite sets at the beginning of each loop";
    "--verbose_loop", Arg.Set Rewrite_rule.verbose_loop, "Display rewrite sets at the beginning of each loop";
    "-vn", Arg.Set Rewrite_rule.verbose_normalisation, "Display new rules normalised";
    "--verbose_normalisation", Arg.Set Rewrite_rule.verbose_normalisation, "Display new rules normalised";
    "-va", Arg.Set Rewrite_rule.verbose_augmented_R, "Display the new rules added to the constraint system R";
    "--verbose_added", Arg.Set Rewrite_rule.verbose_augmented_R, "Display the new rules added to the constraint system R";
    "-vu", Arg.Set Rewrite_rule.verbose_unifiers, "Display the unification queries and the number of most general unifiers";
    "--verbose_unifiers", Arg.Set Rewrite_rule.verbose_unifiers, "Display the unification queries and the number of most general unifiers";
    "-vf", Arg.Set Rewrite_rule.verbose_flattened, "Display the terms in their flattened form";
    "--verbose_flattened", Arg.Set Rewrite_rule.verbose_flattened, "Display the terms in their flattened form";
    "-dp", Arg.Clear Rewrite_rule.pretty, "Disable pretty display of rewrite rules and equations";
    "--disable_pretty", Arg.Clear Rewrite_rule.pretty, "Disable pretty display of rewrite rules and equations";
    "-oc", Arg.Unit (fun () -> Order.order_chosen := CountSymbol; Order.fixed_order := true), "Change the computed order to CountingSymbol";
    "--order_count_symbol", Arg.Unit (fun () -> Order.order_chosen := CountSymbol; Order.fixed_order := true), "Change the computed order to CountingSymbol";
    "-or", Arg.Unit (fun () -> Order.order_chosen := ACRPO; Order.fixed_order := true), "Change the computed order to AC-RPO";
    "--order_ac_rpo", Arg.Unit (fun () -> Order.order_chosen := ACRPO; Order.fixed_order := true), "Change the computed order to AC-RPO";
    "-ve", Arg.Set Rewrite_rule.verbose_everyrule, "Display every computed rule";
    "--verbose_every", Arg.Set Rewrite_rule.verbose_everyrule, "Display every computed rule";
    "-nu", Arg.Clear Rewrite_rule.update_Rn, "Prevent the update of the rewrite system Rn";
    "--no_update_Rn", Arg.Clear Rewrite_rule.update_Rn, "Prevent the update of the rewrite system Rn";
    
    ]
  analyze_file ("Prototype Finite Variant Property generator")