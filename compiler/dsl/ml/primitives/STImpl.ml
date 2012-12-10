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

type 'a axiom_ST = unit -> 'a

let axiom_STBind b k () = let v = b () in k v ()

let axiom_STReturn v () = v

let axiom_STContra () = failwith "ST Contradiction"

let axiom_STWeaken x = x

let axiom_STStrengthen x = x
 
let axiom_STNew v () = ref (Obj.repr v)

let axiom_STFree _ () = ()

let axiom_STRead p () = Obj.obj !p

let axiom_STWrite p v () = p := Obj.repr v

(** ((a -> (unit -> b)) -> a -> (unit -> b)) -> a -> (unit -> b) **)
let axiom_STFix f = 
  let rec fix a () = f fix a ()
  in fix

let exec io = io ()
