(* This code was taken from the source code of the DeepSec verifier and modified by Vincent Cheval *)

(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

(*************
  Statistic
**************)

type stat

val record_tail : stat -> ((unit -> 'a) -> 'b) -> (unit -> 'a) -> 'b

val record_notail : stat -> (unit -> 'a) -> 'a

(******* The function recorded ******)

val reset : unit -> unit 

val time_compare_strong : stat
val time_maude_matching : stat
val time_exists_matching : stat
val time_exists_matching_with_context : stat
val time_matching_with_context_one : stat
val time_subterm : stat
val time_unify : stat
val time_subsumes_strict_ext : stat
val time_overlap_rules : stat
val time_add : stat
val time_generate_extended_signature : stat

val display_statistic : unit -> unit
