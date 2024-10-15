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

type 'a queue

val is_empty : 'a queue -> bool

val iter : 'a queue -> ('a -> unit) -> unit

val exists : 'a queue -> ('a -> bool) -> bool

val filter : 'a queue -> ('a -> bool) -> unit

val add : 'a queue -> 'a -> int -> unit

val length : 'a queue -> int

val clear : 'a queue -> unit

val new_queue : unit -> 'a queue

val get : 'a queue -> 'a option