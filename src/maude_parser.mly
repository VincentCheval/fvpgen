%{

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

open Maude_function
open Term
%}


%token Sharp, Percent
%token EOF
%token VariantUnify, Unify, GetVariants, Reduce, Match
%token In, Empty
%token Ms, Cpu, Real, Second
%token Unifier, Variant, Result, Solution, Matcher
%token Maude, Line1
%token <string> Identifier
%token <int> Number
%token <int> FreshVariable
%token <int> OldVariable
%token Equals, Dot, Slash, Comma, Colon, Arrow
%token EqualUnify, EqualMatch
%token LeftP RightP LBracket RBracket
%token Zero, FakeType
%token Plus
%token NoUnifiers NoUnifier NoMatch
%token NoMoreUnifiers NoMoreVariants
%token Rewrites Decisiontimeline Tilde
%token Bool True False
%token Greater
%token Bitstring
%token Maude
%token Bye

%start unification equality matching

%type < (Term.variable * Term.term) list list > unification
%type < bool > equality
%type < (Term.variable * Term.term) list list > matching

%%
unification:
	| firstLine unifierPreamble unifierList fakeQuery { $3 }

equality:
	| firstLine equalsPreamble rewritesline Result Bool Colon bool { $7 }

matching:
	| firstLine matchingPreamble matchingList fakeQuery { $3 }

fakeQuery:
	| firstLine Match In Identifier Colon Identifier Colon FakeType EqualMatch Identifier Colon FakeType Dot Decisiontimeline
		Matcher Number Identifier Colon FakeType Arrow Identifier Colon FakeType
	{ }


firstLine:
	| Line1 { }
	| Maude Line1 { }

/* AC-Equality */

rewritesline:
	| Rewrites Colon Number In Ms Cpu LeftP Ms Real RightP LeftP rewritepersec {}

rewritepersec:
	| Number Rewrites Slash Second RightP {}
	| Tilde Rewrites Slash Second RightP {}

/* AC-UNIFICATION */
    
unifierPreamble:
 	| Unify In Identifier Colon term EqualUnify term Dot Decisiontimeline{ }
     
unifierList:
	| NoUnifier { [] }
	| unifier {[$1]}
	| unifier unifierList { $1::$2 }

unifier:
 	| Unifier Number substitution { $3 }

/* AC-MATCH */

matchingPreamble:
	| Match limit In Identifier Colon termseq EqualMatch termseq  Dot Decisiontimeline{ }

limit:
	| {}
	| LBracket Number RBracket {}
     
matchingList:
	| NoMatch { [] }
	| matcher {[$1]}
	| matcher matchingList { $1::$2 }

matcher:
 	| Matcher Number substitution { $3 }

equalsPreamble:
 | Reduce In Identifier Colon term Equals Equals term Dot { }
     
term:
 	| OldVariable Colon Bitstring { Var (get_old_variable $1) }
	| FreshVariable Colon Bitstring { Var (get_fresh_variable $1) }
	| Identifier { 
			let f = get_symbol $1 in
			Func(f,[]) }
 	| Identifier LeftP termlist RightP { 
			let f = get_symbol $1 in
			Func(f,$3) }

termseq:
	| term {}
	| term termseq {}

termlist:
 | { [] }
 | netermlist {	$1 }

netermlist:
 | term { [ $1 ] }
 | term Comma netermlist { $1 :: $3 }

substitution:
 | Empty { [] }
 | { [] }
 | assignment substitution { $1 :: $2 }

assignment:
 | OldVariable Colon Bitstring Arrow term  { (get_old_variable $1, $5) }

bool:
 | True  {true}     
 | False {false}     

%%