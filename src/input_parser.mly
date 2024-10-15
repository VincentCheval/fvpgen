%{
	
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
open Input_function

%}

%token Slash, Comma
%token Less, Equals
%token Amin, Bin, Name, AC
%token LPar, RPar, Dot, LBracket, RBracket
%token EOF
%token TRwSys, EqTh, CRwSys
%token RArrow

%token <string> Identifier
%token <int> Number

%start all

%type < (Input_function.parsed_input list * ((Input_function.parsed_term * Input_function.parsed_term) list * bool) option * (Input_function.parsed_term * Input_function.parsed_term) list) > all

%%
all:
	| declaration_list EqTh equation_list EOF { $1, None, $3 }
	| declaration_list TRwSys rewrite_list EqTh equation_list EOF { $1, Some ($3,false), $5 }
	| declaration_list CRwSys rewrite_list EqTh equation_list EOF { $1, Some ($3,true), $5 }

declaration_list :
	| declaration { [ $1 ] }
	| declaration declaration_list { $1 :: $2 }

declaration:
	| functionDeclaration { $1 }
	| orderDeclaration { $1 }

equation_list :
	| equationDeclaration { [$1] }
	| equationDeclaration equation_list { $1 :: $2 }

functionDeclaration:
	| Identifier Slash Number Dot { FuncDecl ($1,$3,true) }
	| Identifier Slash Number LBracket AC RBracket Dot { FuncDecl ($1,$3,false) }

orderDeclaration:
	| Identifier orderList Dot { FuncOrder($1 :: $2) }

orderList:
	| Less Identifier { [$2] }
	| Less Identifier orderList { $2 :: $3 }

equationDeclaration:
	| term Equals term Dot { ($1,$3) }

rewrite_list :
	| rewrite { [$1] }
	| rewrite rewrite_list { $1 :: $2 }

rewrite:
	| term RArrow term Dot { ($1,$3) }

term:
	| Identifier { PIdent $1 }
	| Identifier LPar term_list RPar { PFunc($1,$3) }

term_list:
	| term { [$1] }
	| term Comma term_list { $1 :: $3 }   

%%