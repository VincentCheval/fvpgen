(****************************************************************************)
(* This code was originally taken from AKiSs and modified by Vincent Cheval *)
(* 																			                                    *)
(* Authors of AKiSs: Baelde, Ciobaca, Delaune, Kremer 		                  *)
(* Author of FVPgen: Vincent Cheval                     	                  *)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

{
  open Maude_parser
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
let letters = letter (('.'| '_' | '-' | letter | digit) * )

  rule token = parse
    "\010" | "\013" | "\013\010"
     { Lexing.new_line lexbuf; token lexbuf }
  | [ ' ' '\009' '\012'] +
      { token lexbuf }
  | "==========================================" { debug "Line1"; Line1 }
  | "Maude>" { debug "Maude"; Maude}
  | "No unifiers." { debug "NoUnifiers"; NoUnifiers }
  | "No unifier." { debug "NoUnifier"; NoUnifier }
  | "No match."   { debug "NoMatch"; NoMatch }
  | "empty substitution"   { debug "NoMatch"; Empty }
  | "No more unifiers." { debug "NoMoreUnifiers"; NoMoreUnifiers }
  | "Unifier" { debug "Unifier"; Unifier }
  | "unify" { debug "Unify"; Unify }
  | "match" { debug "Match"; Match }
  | "result" { debug "Result"; Result }
  | "reduce" { debug "Reduce"; Reduce }
  | "rewrites" { debug "Rewrites"; Rewrites }
  | "FakeType" { debug "FakeType"; FakeType }
  | "Matcher" { debug "Matcher"; Matcher }
  | "Solution" { debug "Solution"; Solution }
  | "Bool" { debug "Bool"; Bool}
  | "Bitstring" { debug "Bitstring"; Bitstring }
  | "Decision time: " digits "ms cpu (" digits "ms real)" { debug "Desiontimeline"; Decisiontimeline }
  | "in" { debug "In"; In }
  | digits "ms" { debug "Ms"; Ms }
  | "cpu" { debug "Cpu"; Cpu }
  | "real" { debug "Real"; Real }
  | "second" { debug "Second"; Second }
  | "true" { debug "True"; True}
  | "false" { debug "False"; False}
  | "-->" { debug "Arrow"; Arrow}
  | "/" { debug "Slash"; Slash }
  | "," { debug "Comma"; Comma }
  | ":" { debug "Colon"; Colon }
  | ">" { debug "Greater"; Greater }
  | "=" { debug "Equals"; Equals }
  | "=?" { debug "EqualUnify"; EqualUnify }
  | "<=?" { debug "EqualMatch"; EqualMatch }
  | "(" { debug "LeftP"; LeftP }
  | ")" { debug "RightP"; RightP }
  | "[" { debug "LBracket"; LBracket }
  | "]" { debug "RBracket"; RBracket }
  | "." { debug "Dot"; Dot }
  | "~" { debug "Tilde"; Tilde }
  | "Bye." { debug "Bye"; Bye }
  | ("+" ['0' - '9']*) as i  { Identifier i }
  | ("*" ['0' - '9']*) as i { Identifier i }

  | "X" (digits as n) { debug (Printf.sprintf "X%s" n); OldVariable (int_of_string n) }
  | "#" (digits as n) { debug (Printf.sprintf "#%s" n); FreshVariable (int_of_string n) }
  | "%" (digits as n) { debug (Printf.sprintf "%%%s" n); FreshVariable (int_of_string n) }

  | digits as n { debug (Printf.sprintf "Digits %s" n); Number (int_of_string n) }
  | letters as s { debug (Printf.sprintf "Identifier %s" s); Identifier s }
  

  | '\n' { debug "Nline"; incr_linenum lexbuf; token lexbuf }
  
  | eof { debug "EOF"; EOF }
  | _ { failwith (Printf.sprintf "Illegal character: %s" (Lexing.lexeme lexbuf)) }