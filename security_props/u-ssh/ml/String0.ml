open Datatypes

(** val string_rect :
    'a1 -> (MlCoq.ascii -> MlCoq.ascii list -> 'a1 -> 'a1) ->
    MlCoq.ascii list -> 'a1 **)

let rec string_rect f f0 = function
| [] -> f
| a::s0 -> f0 a s0 (string_rect f f0 s0)

(** val string_rec :
    'a1 -> (MlCoq.ascii -> MlCoq.ascii list -> 'a1 -> 'a1) ->
    MlCoq.ascii list -> 'a1 **)

let rec string_rec f f0 = function
| [] -> f
| a::s0 -> f0 a s0 (string_rec f f0 s0)

(** val string_dec : MlCoq.ascii list -> MlCoq.ascii list -> bool **)

let rec string_dec s s0 =
  match s with
  | [] ->
    (match s0 with
     | [] -> true
     | a::s1 -> false)
  | a::s1 ->
    (match s0 with
     | [] -> false
     | a0::s2 -> if (=) a a0 then string_dec s1 s2 else false)

(** val append : MlCoq.ascii list -> MlCoq.ascii list -> MlCoq.ascii list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val length : MlCoq.ascii list -> MlCoq.nat **)

let rec length = function
| [] -> MlCoq.O
| c::s' -> MlCoq.S (length s')

(** val get : MlCoq.nat -> MlCoq.ascii list -> MlCoq.ascii option **)

let rec get n = function
| [] -> None
| c::s' ->
  (match n with
   | MlCoq.O -> Some c
   | MlCoq.S n' -> get n' s')

(** val substring :
    MlCoq.nat -> MlCoq.nat -> MlCoq.ascii list -> MlCoq.ascii list **)

let rec substring n m s =
  match n with
  | MlCoq.O ->
    (match m with
     | MlCoq.O -> []
     | MlCoq.S m' ->
       (match s with
        | [] -> s
        | c::s' -> c::(substring MlCoq.O m' s')))
  | MlCoq.S n' ->
    (match s with
     | [] -> s
     | c::s' -> substring n' m s')

(** val prefix : MlCoq.ascii list -> MlCoq.ascii list -> bool **)

let rec prefix s1 s2 =
  match s1 with
  | [] -> true
  | a::s1' ->
    (match s2 with
     | [] -> false
     | b::s2' -> if (=) a b then prefix s1' s2' else false)

(** val index :
    MlCoq.nat -> MlCoq.ascii list -> MlCoq.ascii list -> MlCoq.nat option **)

let rec index n s1 s2 = match s2 with
| [] ->
  (match n with
   | MlCoq.O ->
     (match s1 with
      | [] -> Some MlCoq.O
      | a::s1' -> None)
   | MlCoq.S n' -> None)
| b::s2' ->
  (match n with
   | MlCoq.O ->
     if prefix s1 s2
     then Some MlCoq.O
     else (match index MlCoq.O s1 s2' with
           | Some n0 -> Some (MlCoq.S n0)
           | None -> None)
   | MlCoq.S n' ->
     (match index n' s1 s2' with
      | Some n0 -> Some (MlCoq.S n0)
      | None -> None))

(** val findex :
    MlCoq.nat -> MlCoq.ascii list -> MlCoq.ascii list -> MlCoq.nat **)

let findex n s1 s2 =
  match index n s1 s2 with
  | Some n0 -> n0
  | None -> MlCoq.O

(** val coq_HelloWorld : MlCoq.ascii list **)

let coq_HelloWorld =
  (MlCoq.Ascii (true, false, false, true, false, false, false,
    false))::((MlCoq.Ascii (false, true, false, false, false, true, false,
    false))::((MlCoq.Ascii (false, false, false, true, false, false, true,
    false))::((MlCoq.Ascii (true, false, true, false, false, true, true,
    false))::((MlCoq.Ascii (false, false, true, true, false, true, true,
    false))::((MlCoq.Ascii (false, false, true, true, false, true, true,
    false))::((MlCoq.Ascii (true, true, true, true, false, true, true,
    false))::((MlCoq.Ascii (false, false, false, false, false, true, false,
    false))::((MlCoq.Ascii (true, true, true, false, true, true, true,
    false))::((MlCoq.Ascii (true, true, true, true, false, true, true,
    false))::((MlCoq.Ascii (false, true, false, false, true, true, true,
    false))::((MlCoq.Ascii (false, false, true, true, false, true, true,
    false))::((MlCoq.Ascii (false, false, true, false, false, true, true,
    false))::((MlCoq.Ascii (true, false, false, false, false, true, false,
    false))::((MlCoq.Ascii (false, true, false, false, false, true, false,
    false))::((MlCoq.Ascii (true, true, true, false, false, false, false,
    false))::((MlCoq.Ascii (false, true, false, true, false, false, false,
    false))::[]))))))))))))))))

