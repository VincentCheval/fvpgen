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

type parsed_term = 
  | PIdent of string
  | PFunc of string * parsed_term list

type parsed_input = 
  | FuncDecl of string * int * bool
  | FuncOrder of string list

module StringComp = struct
  type t = string
  let compare = compare
end

module StringMap = Map.Make(StringComp)

let get_variable env s = 
  match StringMap.find_opt s !env with
  | Some v -> v
  | None -> 
      let v = fresh_variable () in
      env := StringMap.add s (Var v) !env;
      Var v

let rec parse_functions = function
  | [] -> []
  | FuncDecl(s,n,syntactic) :: q -> 
      if syntactic 
      then (s,n,Syntactic) :: parse_functions q
      else  (s,n,AC) :: parse_functions q
  | _ :: q -> parse_functions q

let rec parse_order = function
  | [] -> []
  | FuncDecl(s,n,syntactic) :: q -> 
      if syntactic 
      then (s,n,Syntactic) :: parse_functions q
      else  (s,n,AC) :: parse_functions q
  | _ :: q -> parse_functions q

let rec parse_order = function
  | [] -> failwith "Order should be defined for each symbol."
  | (FuncOrder l) :: _-> l
  | _::q -> parse_order q

let rec parse_term vars = function
  | PIdent s ->
      begin match List.find_opt (fun f -> f.f_name = s) !all_symbols with
      | Some f -> 
          if f.f_arity <> 0
          then failwith (Printf.sprintf "Wrong arity of symbol %s. Declared with %d, used with 0" f.f_name f.f_arity);

          Func(f,[])
      | None -> get_variable vars s
      end
  | PFunc(s,args) ->
      match List.find_opt (fun f -> f.f_name = s) !all_symbols with
      | None -> failwith (Printf.sprintf "The function symbol %s is not declared" s)
      | Some f -> 
          if f.f_arity <> List.length args
          then failwith (Printf.sprintf "Wrong arity of symbol %s. Declared with %d, used with %d" f.f_name f.f_arity (List.length args));

          Func(f,List.map (parse_term vars) args)

let rec parse_equations = function
  | [] -> []
  | (t1,t2) :: q ->
      let vars = ref StringMap.empty in
      let s1 = parse_term vars t1 in
      let s2 = parse_term vars t2 in
      let rw = 
        Term.auto_cleanup (fun () ->
          refresh_term s1, refresh_term s2
        ) 
      in
      rw :: parse_equations q
        
let parse_declarations decl_list rwsysRn_op eqE =

  let list_symb = parse_functions decl_list in

  let symb_order = parse_order decl_list in

  let ordered_symb = 
    List.map (fun f_name ->
      match List.find_opt (fun (s,_,_) -> s = f_name) list_symb with
      | None -> failwith "Ordered symbol should be defined."
      | Some(_,n,cat) -> (f_name,n,cat)
    ) symb_order
  in

  initialise_symbols ordered_symb;

  let rwsysRn_op = match rwsysRn_op with 
    | None -> None
    | Some (rwlist,b)  -> Some (parse_equations rwlist,b )
  in
  
  rwsysRn_op, parse_equations eqE