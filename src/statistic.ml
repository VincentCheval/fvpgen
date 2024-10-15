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

let record_time = true

let initial_time = (Unix.times ()).Unix.tms_utime

type stat =
  {
    mutable time : float;
    mutable call : int;
    mutable time_last_restarted : float;
    name : string;
  }

let current_recording = ref []

let record_tail =
  if record_time
  then
    (fun ref_t f_cont f_next ->
      let t0 = (Unix.times ()).Unix.tms_utime in

      (* We stop the current recording *)
      begin match !current_recording with
        | [] -> ()
        | ref_t'::_ -> ref_t'.time <- ref_t'.time +. t0 -. ref_t'.time_last_restarted
      end;

      (* We add the new recording time *)
      ref_t.time_last_restarted <- t0;
      ref_t.call <- ref_t.call + 1;
      current_recording := ref_t::!current_recording;

      f_cont (fun () ->
        (* We stop the clock *)
        let t1 = (Unix.times ()).Unix.tms_utime in
        ref_t.time <- ref_t.time +. t1 -. ref_t.time_last_restarted;
        begin match !current_recording with
          | _::((ref_t'::_) as q) ->
              ref_t'.time_last_restarted <- t1;
              current_recording := q
          | _::q -> current_recording := q
          | _ -> failwith "[statistic.ml >> record_time] There should be at least one recorder."
        end;
        f_next ()
      )
    )
  else (fun _ f_cont f_next -> f_cont f_next)

let record_notail =
  if record_time
  then
    (fun ref_t f_cont ->
      let t0 = (Unix.times ()).Unix.tms_utime in

      (* We stop the current recording *)
      begin match !current_recording with
        | [] -> ()
        | ref_t'::_ -> ref_t'.time <- ref_t'.time +. t0 -. ref_t'.time_last_restarted
      end;

      (* We add the new recording time *)
      ref_t.time_last_restarted <- t0;
      ref_t.call <- ref_t.call + 1;
      current_recording := ref_t::!current_recording;

      let res = f_cont () in

      (* We stop the clock *)
      let t1 = (Unix.times ()).Unix.tms_utime in
      ref_t.time <- ref_t.time +. t1 -. ref_t.time_last_restarted;
      begin match !current_recording with
        | _::((ref_t'::_) as q) ->
            ref_t'.time_last_restarted <- t1;
            current_recording := q
        | _::q -> current_recording := q
        | _ -> failwith "[statistic.ml >> record_time] There should be at least one recorder."
      end;

      res
    )
  else (fun _ f_cont -> f_cont ())

(******* The function recorded ******)

let recorder_list = ref []

let create name =
  let r = { name = name; time = 0.; call = 0; time_last_restarted = 0. } in
  recorder_list := r :: ! recorder_list;
  r

let reset =
  if record_time
  then
    (fun () ->
      List.iter (fun r -> r.time <- 0.; r.call <- 0; r.time_last_restarted <- 0. ) !recorder_list;
      current_recording := []
    )
  else (fun _ -> ())

let time_compare_strong = create "compare_strong"
let time_maude_matching = create "maude_matching"
let time_exists_matching = create "exists_matching"
let time_exists_matching_with_context = create "exists_matching_with_context"

let time_matching_with_context_one = create "matching_with_context_one"
let time_subterm = create "subterm"
let time_unify = create "unify"

let time_subsumes_strict_ext = create "subsumes_strict_ext"
let time_add = create "add"
let time_overlap_rules = create "overlap_rules"
let time_generate_extended_signature = create "generate_extended_signature"

let display_statistic () =
  if record_time
  then
    List.iter (fun r ->
      Printf.printf "%s: %fs (%d calls)\n" r.name r.time r.call
    ) !recorder_list
