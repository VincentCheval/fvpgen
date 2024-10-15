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

type 'a queue = { mutable q : (int * 'a Pvqueue.q) list }

let is_empty q = q.q = []

let iter q f = List.iter (fun (_,sq) -> Pvqueue.iter sq f) q.q

let exists q f = List.exists (fun (_,sq) -> Pvqueue.exists sq f) q.q

let filter queue f = 
  queue.q <- 
    List.filter (fun (i,sq) ->
      Pvqueue.filter sq f;
      not (Pvqueue.is_empty sq)
    ) queue.q

let rec add_aux queue elt k = match queue with
  | [] -> 
      let sq = Pvqueue.new_queue () in
      Pvqueue.add sq elt;
      [(k,sq)]
  | (k',_)::_ when k < k' -> 
      let sq = Pvqueue.new_queue () in
      Pvqueue.add sq elt;
      (k,sq) :: queue
  | (k',sq)::_ when k = k' -> Pvqueue.add sq elt; queue
  | h::q -> h :: add_aux q elt k

let add queue elt k = queue.q <- add_aux queue.q elt k

let clear queue = queue.q <- []

let new_queue () = { q = [] }

let rec get queue = match queue.q with
  | [] -> None
  | (k,sq)::q -> 
      match Pvqueue.get sq with
      | None -> queue.q <- q; get queue
      | Some elt -> Some elt

let length queue =
  List.fold_left (fun acc (_,q) -> Pvqueue.length q + acc) 0 queue.q