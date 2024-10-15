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
{
  open Input_parser
  open Term

  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }

  let do_debug = false

  let debug str = if do_debug then (Printf.printf "Token [%s]\n" str; flush_all ())
}

let digit = ['0' - '9']
let digits = digit +
let lower = ['a' - 'z']
let upper = ['A' - 'Z']
let letter = lower | upper
let letters = letter (( '_' | letter | digit) * )

  rule token = parse
    "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; token lexbuf }
  | [ ' ' '\009' '\012'] +
      { token lexbuf }
  | "=== Equational Theory" { debug "EqTh"; EqTh }
  | "=== Terminating Rewrite System" { debug "TRsys"; TRwSys }
  | "=== Convergent Rewrite System" { debug "CRsys"; CRwSys }
  | "amin"  { debug "Amin"; Amin }
  | "bin"   { debug "Bin"; Bin }
  | "name"  { debug "Name"; Name }
  | "AC"  { debug "AC"; AC }
  | "/" { debug "Slash"; Slash }
  | "," { debug "Comma"; Comma }
  | "<" { debug "Less"; Less }
  | "->" { debug "RArrow"; RArrow }
  | "=" { debug "Equals"; Equals }
  | "(*" {
         comment lexbuf;
         token lexbuf
       }
  | "(" { debug "Lpar"; LPar }
  | ")" { debug "Rpar"; RPar }
  | "[" { debug "LBracket"; LBracket }
  | "]" { debug "RBracket"; RBracket }
  | "." { debug "Dot"; Dot }

  | digits as n { debug ("Number "^n); Number (int_of_string n) }
  | letters as s { debug ("Identifier "^s); Identifier s }

  | '\n' { incr_linenum lexbuf; token lexbuf }
  
  | eof { EOF }
  | _ { failwith (Printf.sprintf "Illegal character: %s" (Lexing.lexeme lexbuf)) }

and comment = parse
| "*)" { }
| "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; comment lexbuf }
| eof { }
| _ { comment lexbuf }