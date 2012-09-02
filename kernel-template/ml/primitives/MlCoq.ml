(* Copyright (c) 2009, Harvard University
 * All rights reserved.
 *
 * Authors: Gregory Malecha, Ryan Wisnesky
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

(** Coq Extraction Definitions **)
type ascii =
  | Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type nat =
  | O
  | S of nat

(** Helpful functions **)
let int_to_nat =
  let rec f i acc =
    if i = 0 then 
      acc
    else
      f (i - 1) (S acc)
  in 
  fun i -> 
    if i < 0 then 
      failwith "iton : negative number!"
    else 
      f i O

let nat_to_int =
  let rec f acc n =
    match n with
    | O -> acc
    | S m -> f (1 + acc) m
  in
  f 0

let ascii_to_char asc = 
  let Ascii (a, b, c, d, e, f, g, h) = asc in
  let bits : bool list = [a;b;c;d;e;f;g;h] in
  let ch = List.fold_right (fun v a -> a * 2 + if v then 1 else 0) bits 0 in
  Char.chr ch

let list_ascii_to_string s = 
  let rec r s =
    match s with
      [] -> ""
    | first :: rest ->
	(String.make 1 (ascii_to_char first)) ^ (r rest)
  in r s
