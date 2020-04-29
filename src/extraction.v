(** Extraction to OCaml. **)
(* (C) M. Bodin - see LICENSE.txt *)

Require Import Extraction.
From Wasm Require Import binary_parser type_checker interpreter.

Extraction Language OCaml.

Extraction "Extract" parse_wasm cl_type_check run_v.

