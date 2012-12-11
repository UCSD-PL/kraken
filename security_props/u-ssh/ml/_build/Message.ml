open Ascii
open Datatypes
open NPeano
open Peano
open STsep
open Specif

type __ = Obj.t

type str = MlCoq.ascii list

type num =
  (MlCoq.ascii, MlCoq.ascii) prod
  (* singleton inductive, whose constructor was Num *)

(** val num_rect : ((MlCoq.ascii, MlCoq.ascii) prod -> 'a1) -> num -> 'a1 **)

let num_rect f n =
  f n

(** val num_rec : ((MlCoq.ascii, MlCoq.ascii) prod -> 'a1) -> num -> 'a1 **)

let num_rec f n =
  f n

(** val nat_of_num : num -> MlCoq.nat **)

let nat_of_num = function
| Coq_pair (l, h) ->
  plus (nat_of_ascii l)
    (mult (nat_of_ascii h) (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S
      MlCoq.O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val num_of_nat : MlCoq.nat -> num **)

let num_of_nat n =
  let l =
    modulo n (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S
      MlCoq.O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  let h =
    div n (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
      (MlCoq.S
      MlCoq.O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  Coq_pair ((ascii_of_nat l), (ascii_of_nat h))

(** val str_of_string : MlCoq.ascii list -> str **)

let rec str_of_string = function
| [] -> []
| c::rest -> c::(str_of_string rest)

type chan_type =
| System
| Slave

(** val chan_type_rect : 'a1 -> 'a1 -> chan_type -> 'a1 **)

let chan_type_rect f f0 = function
| System -> f
| Slave -> f0

(** val chan_type_rec : 'a1 -> 'a1 -> chan_type -> 'a1 **)

let chan_type_rec f f0 = function
| System -> f
| Slave -> f0

(** val chan_path : chan_type -> str **)

let chan_path = function
| System ->
  str_of_string ((MlCoq.Ascii (true, true, false, false, true, true, true,
    false))::((MlCoq.Ascii (true, false, false, true, true, true, true,
    false))::((MlCoq.Ascii (true, true, false, false, true, true, true,
    false))::((MlCoq.Ascii (false, false, true, false, true, true, true,
    false))::((MlCoq.Ascii (true, false, true, false, false, true, true,
    false))::((MlCoq.Ascii (true, false, true, true, false, true, true,
    false))::[]))))))
| Slave ->
  str_of_string ((MlCoq.Ascii (true, true, false, false, true, true, true,
    false))::((MlCoq.Ascii (false, false, true, true, false, true, true,
    false))::((MlCoq.Ascii (true, false, false, false, false, true, true,
    false))::((MlCoq.Ascii (false, true, true, false, true, true, true,
    false))::((MlCoq.Ascii (true, false, true, false, false, true, true,
    false))::[])))))

type chan = KrakenImpl.chan

type st_System =
| Build_st_System

(** val st_System_rect : 'a1 -> 'a1 **)

let st_System_rect f =
  f

(** val st_System_rec : 'a1 -> 'a1 **)

let st_System_rec f =
  f

type st_Slave =
| Build_st_Slave

(** val st_Slave_rect : 'a1 -> 'a1 **)

let st_Slave_rect f =
  f

(** val st_Slave_rec : 'a1 -> 'a1 **)

let st_Slave_rec f =
  f

type comp_state = __

type tchan = (chan_type, (chan, comp_state) prod) sigT

(** val tchan_eq : tchan -> tchan -> bool **)

let tchan_eq = KrakenImpl.tchan_eq

type fdesc = KrakenImpl.fdesc

type coq_Action =
| Exec of str * tchan
| Call of str * str * fdesc
| Select of tchan list * tchan
| Recv of tchan * str
| Send of tchan * str
| RecvFD of tchan * fdesc
| SendFD of tchan * fdesc

(** val coq_Action_rect :
    (str -> tchan -> 'a1) -> (str -> str -> fdesc -> 'a1) -> (tchan list ->
    tchan -> 'a1) -> (tchan -> str -> 'a1) -> (tchan -> str -> 'a1) -> (tchan
    -> fdesc -> 'a1) -> (tchan -> fdesc -> 'a1) -> coq_Action -> 'a1 **)

let coq_Action_rect f f0 f1 f2 f3 f4 f5 = function
| Exec (x, x0) -> f x x0
| Call (x, x0, x1) -> f0 x x0 x1
| Select (x, x0) -> f1 x x0
| Recv (x, x0) -> f2 x x0
| Send (x, x0) -> f3 x x0
| RecvFD (x, x0) -> f4 x x0
| SendFD (x, x0) -> f5 x x0

(** val coq_Action_rec :
    (str -> tchan -> 'a1) -> (str -> str -> fdesc -> 'a1) -> (tchan list ->
    tchan -> 'a1) -> (tchan -> str -> 'a1) -> (tchan -> str -> 'a1) -> (tchan
    -> fdesc -> 'a1) -> (tchan -> fdesc -> 'a1) -> coq_Action -> 'a1 **)

let coq_Action_rec f f0 f1 f2 f3 f4 f5 = function
| Exec (x, x0) -> f x x0
| Call (x, x0, x1) -> f0 x x0 x1
| Select (x, x0) -> f1 x x0
| Recv (x, x0) -> f2 x x0
| Send (x, x0) -> f3 x x0
| RecvFD (x, x0) -> f4 x x0
| SendFD (x, x0) -> f5 x x0

type coq_Trace = coq_Action list

(** val exec : chan_type -> str -> comp_state -> tchan coq_STsep **)

let exec = KrakenImpl.exec

(** val call : str -> str -> fdesc coq_STsep **)

let call = KrakenImpl.call

(** val select : tchan list -> tchan coq_STsep **)

let select = KrakenImpl.select

(** val recv : tchan -> num -> str coq_STsep **)

let recv = KrakenImpl.recv

(** val send : tchan -> str -> unit coq_STsep **)

let send = KrakenImpl.send

(** val recv_fd : tchan -> fdesc coq_STsep **)

let recv_fd = KrakenImpl.recv_fd

(** val send_fd : tchan -> fdesc -> unit coq_STsep **)

let send_fd = KrakenImpl.send_fd

(** val coq_RecvNum : tchan -> num -> coq_Trace **)

let coq_RecvNum c = function
| Coq_pair (l, h) -> (Recv (c, (h::(l::[]))))::[]

(** val recv_num : tchan -> num coq_STsep **)

let recv_num c =
  coq_SepBind
    (coq_SepStrengthen
      (recv c (Coq_pair ((MlCoq.Ascii (false, true, false, false, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false)))))) (fun s ->
    match s with
    | [] ->
      coq_SepWeaken
        (coq_SepStrengthen
          (coq_SepFrame
            (coq_SepReturn (Coq_pair ((MlCoq.Ascii (false, false, false,
              false, false, false, false, false)), (MlCoq.Ascii (false,
              false, false, false, false, false, false, false)))))))
    | h::l0 ->
      (match l0 with
       | [] ->
         coq_SepWeaken
           (coq_SepStrengthen
             (coq_SepFrame
               (coq_SepReturn (Coq_pair ((MlCoq.Ascii (false, false, false,
                 false, false, false, false, false)), (MlCoq.Ascii (false,
                 false, false, false, false, false, false, false)))))))
       | l::l1 ->
         (match l1 with
          | [] ->
            coq_SepWeaken
              (coq_SepStrengthen
                (coq_SepFrame (coq_SepReturn (Coq_pair (l, h)))))
          | a::l2 ->
            coq_SepWeaken
              (coq_SepStrengthen
                (coq_SepFrame
                  (coq_SepReturn (Coq_pair ((MlCoq.Ascii (false, false,
                    false, false, false, false, false, false)), (MlCoq.Ascii
                    (false, false, false, false, false, false, false,
                    false))))))))))

(** val coq_SendNum : tchan -> num -> coq_Trace **)

let coq_SendNum c = function
| Coq_pair (l, h) -> (Send (c, (h::(l::[]))))::[]

(** val send_num : tchan -> num -> unit coq_STsep **)

let send_num c = function
| Coq_pair (l, h) ->
  coq_SepSeq (coq_SepStrengthen (send c (h::(l::[]))))
    (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ()))))

(** val coq_RecvStr : tchan -> str -> coq_Trace **)

let coq_RecvStr c s =
  (Recv (c, s))::(coq_RecvNum c (num_of_nat (length s)))

(** val recv_str : tchan -> str coq_STsep **)

let recv_str c =
  coq_SepBind (coq_SepStrengthen (recv_num c)) (fun n ->
    coq_SepBind (coq_SepStrengthen (recv c n)) (fun s ->
      coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn s)))))

(** val coq_SendStr : tchan -> str -> coq_Trace **)

let coq_SendStr c s =
  (Send (c, s))::(coq_SendNum c (num_of_nat (length s)))

(** val send_str : tchan -> str -> unit coq_STsep **)

let send_str c s =
  let n = num_of_nat (length s) in
  coq_SepSeq (coq_SepStrengthen (send_num c n))
    (coq_SepSeq (coq_SepStrengthen (send c s))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))

(** val coq_Exec_t : str -> tchan -> coq_Trace **)

let coq_Exec_t prog c =
  (Exec (prog, c))::[]

(** val coq_Call_t : str -> str -> fdesc -> coq_Trace **)

let coq_Call_t prog arg f =
  (Call (prog, arg, f))::[]

(** val coq_RecvFD_t : tchan -> fdesc -> coq_Trace **)

let coq_RecvFD_t c f =
  (RecvFD (c, f))::[]

(** val coq_SendFD_t : tchan -> fdesc -> coq_Trace **)

let coq_SendFD_t c f =
  (SendFD (c, f))::[]

type msg =
| LoginReq of str
| LoginRes of num
| PubkeyReq
| PubkeyRes of str
| KeysignReq of str
| KeysignRes of str
| CreatePtyerReq
| CreatePtyerRes of fdesc * fdesc
| SysLoginReq of str
| SysLoginRes of str * num
| SysPubkeyReq
| SysPubkeyRes of str
| SysKeysignReq of str
| SysKeysignRes of str
| SysCreatePtyerReq of str
| SysCreatePtyerRes of fdesc * fdesc
| BadTag of num

(** val msg_rect :
    (str -> 'a1) -> (num -> 'a1) -> 'a1 -> (str -> 'a1) -> (str -> 'a1) ->
    (str -> 'a1) -> 'a1 -> (fdesc -> fdesc -> 'a1) -> (str -> 'a1) -> (str ->
    num -> 'a1) -> 'a1 -> (str -> 'a1) -> (str -> 'a1) -> (str -> 'a1) ->
    (str -> 'a1) -> (fdesc -> fdesc -> 'a1) -> (num -> 'a1) -> msg -> 'a1 **)

let msg_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
| LoginReq x -> f x
| LoginRes x -> f0 x
| PubkeyReq -> f1
| PubkeyRes x -> f2 x
| KeysignReq x -> f3 x
| KeysignRes x -> f4 x
| CreatePtyerReq -> f5
| CreatePtyerRes (x, x0) -> f6 x x0
| SysLoginReq x -> f7 x
| SysLoginRes (x, x0) -> f8 x x0
| SysPubkeyReq -> f9
| SysPubkeyRes x -> f10 x
| SysKeysignReq x -> f11 x
| SysKeysignRes x -> f12 x
| SysCreatePtyerReq x -> f13 x
| SysCreatePtyerRes (x, x0) -> f14 x x0
| BadTag x -> f15 x

(** val msg_rec :
    (str -> 'a1) -> (num -> 'a1) -> 'a1 -> (str -> 'a1) -> (str -> 'a1) ->
    (str -> 'a1) -> 'a1 -> (fdesc -> fdesc -> 'a1) -> (str -> 'a1) -> (str ->
    num -> 'a1) -> 'a1 -> (str -> 'a1) -> (str -> 'a1) -> (str -> 'a1) ->
    (str -> 'a1) -> (fdesc -> fdesc -> 'a1) -> (num -> 'a1) -> msg -> 'a1 **)

let msg_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
| LoginReq x -> f x
| LoginRes x -> f0 x
| PubkeyReq -> f1
| PubkeyRes x -> f2 x
| KeysignReq x -> f3 x
| KeysignRes x -> f4 x
| CreatePtyerReq -> f5
| CreatePtyerRes (x, x0) -> f6 x x0
| SysLoginReq x -> f7 x
| SysLoginRes (x, x0) -> f8 x x0
| SysPubkeyReq -> f9
| SysPubkeyRes x -> f10 x
| SysKeysignReq x -> f11 x
| SysKeysignRes x -> f12 x
| SysCreatePtyerReq x -> f13 x
| SysCreatePtyerRes (x, x0) -> f14 x x0
| BadTag x -> f15 x

(** val coq_RecvMsg : tchan -> msg -> coq_Trace **)

let coq_RecvMsg c = function
| LoginReq p0 ->
  app (coq_RecvStr c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (true, false, false, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| LoginRes p0 ->
  app (coq_RecvNum c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (false, true, false, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| PubkeyReq ->
  coq_RecvNum c (Coq_pair ((MlCoq.Ascii (true, true, false, false, false,
    false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
    false, false, false))))
| PubkeyRes p0 ->
  app (coq_RecvStr c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (false, false, true, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| KeysignReq p0 ->
  app (coq_RecvStr c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (true, false, true, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| KeysignRes p0 ->
  app (coq_RecvStr c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (false, true, true, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| CreatePtyerReq ->
  coq_RecvNum c (Coq_pair ((MlCoq.Ascii (true, true, true, false, false,
    false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
    false, false, false))))
| CreatePtyerRes (p0, p1) ->
  app (coq_RecvFD_t c p1)
    (app (coq_RecvFD_t c p0)
      (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (false, false, false, true,
        false, false, false, false)), (MlCoq.Ascii (false, false, false,
        false, false, false, false, false))))))
| SysLoginReq p0 ->
  app (coq_RecvStr c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (true, false, false, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysLoginRes (p0, p1) ->
  app (coq_RecvNum c p1)
    (app (coq_RecvStr c p0)
      (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (false, true, false, true,
        false, false, false, false)), (MlCoq.Ascii (false, false, false,
        false, false, false, false, false))))))
| SysPubkeyReq ->
  coq_RecvNum c (Coq_pair ((MlCoq.Ascii (true, true, false, true, false,
    false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
    false, false, false))))
| SysPubkeyRes p0 ->
  app (coq_RecvStr c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (false, false, true, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysKeysignReq p0 ->
  app (coq_RecvStr c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (true, false, true, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysKeysignRes p0 ->
  app (coq_RecvStr c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (false, true, true, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysCreatePtyerReq p0 ->
  app (coq_RecvStr c p0)
    (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (true, true, true, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysCreatePtyerRes (p0, p1) ->
  app (coq_RecvFD_t c p1)
    (app (coq_RecvFD_t c p0)
      (coq_RecvNum c (Coq_pair ((MlCoq.Ascii (false, false, false, false,
        true, false, false, false)), (MlCoq.Ascii (false, false, false,
        false, false, false, false, false))))))
| BadTag p0 -> coq_RecvNum c p0

(** val coq_SendMsg : tchan -> msg -> coq_Trace **)

let coq_SendMsg c = function
| LoginReq p0 ->
  app (coq_SendStr c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (true, false, false, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| LoginRes p0 ->
  app (coq_SendNum c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (false, true, false, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| PubkeyReq ->
  coq_SendNum c (Coq_pair ((MlCoq.Ascii (true, true, false, false, false,
    false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
    false, false, false))))
| PubkeyRes p0 ->
  app (coq_SendStr c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (false, false, true, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| KeysignReq p0 ->
  app (coq_SendStr c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (true, false, true, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| KeysignRes p0 ->
  app (coq_SendStr c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (false, true, true, false, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| CreatePtyerReq ->
  coq_SendNum c (Coq_pair ((MlCoq.Ascii (true, true, true, false, false,
    false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
    false, false, false))))
| CreatePtyerRes (p0, p1) ->
  app (coq_SendFD_t c p1)
    (app (coq_SendFD_t c p0)
      (coq_SendNum c (Coq_pair ((MlCoq.Ascii (false, false, false, true,
        false, false, false, false)), (MlCoq.Ascii (false, false, false,
        false, false, false, false, false))))))
| SysLoginReq p0 ->
  app (coq_SendStr c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (true, false, false, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysLoginRes (p0, p1) ->
  app (coq_SendNum c p1)
    (app (coq_SendStr c p0)
      (coq_SendNum c (Coq_pair ((MlCoq.Ascii (false, true, false, true,
        false, false, false, false)), (MlCoq.Ascii (false, false, false,
        false, false, false, false, false))))))
| SysPubkeyReq ->
  coq_SendNum c (Coq_pair ((MlCoq.Ascii (true, true, false, true, false,
    false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
    false, false, false))))
| SysPubkeyRes p0 ->
  app (coq_SendStr c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (false, false, true, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysKeysignReq p0 ->
  app (coq_SendStr c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (true, false, true, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysKeysignRes p0 ->
  app (coq_SendStr c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (false, true, true, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysCreatePtyerReq p0 ->
  app (coq_SendStr c p0)
    (coq_SendNum c (Coq_pair ((MlCoq.Ascii (true, true, true, true, false,
      false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
      false, false, false)))))
| SysCreatePtyerRes (p0, p1) ->
  app (coq_SendFD_t c p1)
    (app (coq_SendFD_t c p0)
      (coq_SendNum c (Coq_pair ((MlCoq.Ascii (false, false, false, false,
        true, false, false, false)), (MlCoq.Ascii (false, false, false,
        false, false, false, false, false))))))
| BadTag p0 ->
  coq_SendNum c (Coq_pair ((MlCoq.Ascii (false, false, false, false, false,
    false, false, false)), (MlCoq.Ascii (false, false, false, false, false,
    false, false, false))))

(** val recv_msg : tchan -> msg coq_STsep **)

let recv_msg c =
  coq_SepBind (coq_SepStrengthen (recv_num c)) (fun tag ->
    let Coq_pair (a, a0) = tag in
    let MlCoq.Ascii (b, b0, b1, b2, b3, b4, b5, b6) = a in
    if b
    then if b0
         then if b1
              then if b2
                   then if b3
                        then let m = Coq_pair ((MlCoq.Ascii (true, true,
                               true, true, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (true, true,
                                    true, true, false, true, b5, b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (true,
                                         true, true, true, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (true, true, true, true, false,
                                              false, false, true)), a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (true, true,
                                                   true, true, false, false,
                                                   false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (true,
                                                        true, true, true,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (true, true,
                                                             true, true,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (true,
                                                                  true, true,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (SysCreatePtyerReq
                                                                    p0)))))
                   else if b3
                        then let m = Coq_pair ((MlCoq.Ascii (true, true,
                               true, false, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (true, true,
                                    true, false, false, true, b5, b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (true,
                                         true, true, false, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (true, true, true, false,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (true, true,
                                                   true, false, false, false,
                                                   false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (true,
                                                        true, true, false,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (true, true,
                                                             true, false,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (true,
                                                                  true, true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    CreatePtyerReq)))
              else if b2
                   then if b3
                        then let m = Coq_pair ((MlCoq.Ascii (true, true,
                               false, true, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (true, true,
                                    false, true, false, true, b5, b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (true,
                                         true, false, true, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (true, true, false, true,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (true, true,
                                                   false, true, false, false,
                                                   false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (true,
                                                        true, false, true,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (true, true,
                                                             false, true,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (true,
                                                                  true,
                                                                  false,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    SysPubkeyReq)))
                   else if b3
                        then let m = Coq_pair ((MlCoq.Ascii (true, true,
                               false, false, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (true, true,
                                    false, false, false, true, b5, b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (true,
                                         true, false, false, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (true, true, false, false,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (true, true,
                                                   false, false, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (true,
                                                        true, false, false,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (true, true,
                                                             false, false,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (true,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    PubkeyReq)))
         else if b1
              then if b2
                   then if b3
                        then let m = Coq_pair ((MlCoq.Ascii (true, false,
                               true, true, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (true,
                                    false, true, true, false, true, b5, b6)),
                                    a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (true,
                                         false, true, true, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (true, false, true, true,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (true,
                                                   false, true, true, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (true,
                                                        false, true, true,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (true, false,
                                                             true, true,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (true,
                                                                  false,
                                                                  true, true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (SysKeysignReq
                                                                    p0)))))
                   else if b3
                        then let m = Coq_pair ((MlCoq.Ascii (true, false,
                               true, false, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (true,
                                    false, true, false, false, true, b5,
                                    b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (true,
                                         false, true, false, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (true, false, true, false,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (true,
                                                   false, true, false, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (true,
                                                        false, true, false,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (true, false,
                                                             true, false,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (true,
                                                                  false,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (KeysignReq
                                                                    p0)))))
              else if b2
                   then if b3
                        then let m = Coq_pair ((MlCoq.Ascii (true, false,
                               false, true, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (true,
                                    false, false, true, false, true, b5,
                                    b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (true,
                                         false, false, true, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (true, false, false, true,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (true,
                                                   false, false, true, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (true,
                                                        false, false, true,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (true, false,
                                                             false, true,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (true,
                                                                  false,
                                                                  false,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (SysLoginReq
                                                                    p0)))))
                   else if b3
                        then let m = Coq_pair ((MlCoq.Ascii (true, false,
                               false, false, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (true,
                                    false, false, false, false, true, b5,
                                    b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (true,
                                         false, false, false, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (true, false, false, false,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (true,
                                                   false, false, false,
                                                   false, false, false,
                                                   false)), (MlCoq.Ascii
                                                   (true, b8, b9, b10, b11,
                                                   b12, b13, b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (true,
                                                        false, false, false,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (true, false,
                                                             false, false,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (LoginReq
                                                                    p0)))))
    else if b0
         then if b1
              then if b2
                   then if b3
                        then let m = Coq_pair ((MlCoq.Ascii (false, true,
                               true, true, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (false,
                                    true, true, true, false, true, b5, b6)),
                                    a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (false,
                                         true, true, true, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (false, true, true, true,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (false,
                                                   true, true, true, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (false,
                                                        true, true, true,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (false, true,
                                                             true, true,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (false,
                                                                  true, true,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (SysKeysignRes
                                                                    p0)))))
                   else if b3
                        then let m = Coq_pair ((MlCoq.Ascii (false, true,
                               true, false, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (false,
                                    true, true, false, false, true, b5, b6)),
                                    a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (false,
                                         true, true, false, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (false, true, true, false,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (false,
                                                   true, true, false, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (false,
                                                        true, true, false,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (false, true,
                                                             true, false,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (false,
                                                                  true, true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (KeysignRes
                                                                    p0)))))
              else if b2
                   then if b3
                        then let m = Coq_pair ((MlCoq.Ascii (false, true,
                               false, true, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (false,
                                    true, false, true, false, true, b5, b6)),
                                    a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (false,
                                         true, false, true, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (false, true, false, true,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (false,
                                                   true, false, true, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (false,
                                                        true, false, true,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (false, true,
                                                             false, true,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (false,
                                                                  true,
                                                                  false,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_num
                                                                    c))
                                                                    (fun p1 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (SysLoginRes
                                                                    (p0,
                                                                    p1)))))))
                   else if b3
                        then let m = Coq_pair ((MlCoq.Ascii (false, true,
                               false, false, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (false,
                                    true, false, false, false, true, b5,
                                    b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (false,
                                         true, false, false, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (false, true, false, false,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (false,
                                                   true, false, false, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (false,
                                                        true, false, false,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (false, true,
                                                             false, false,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (false,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_num
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (LoginRes
                                                                    p0)))))
         else if b1
              then if b2
                   then if b3
                        then let m = Coq_pair ((MlCoq.Ascii (false, false,
                               true, true, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (false,
                                    false, true, true, false, true, b5, b6)),
                                    a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (false,
                                         false, true, true, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (false, false, true, true,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (false,
                                                   false, true, true, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (false,
                                                        false, true, true,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (false, false,
                                                             true, true,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  true, true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (SysPubkeyRes
                                                                    p0)))))
                   else if b3
                        then let m = Coq_pair ((MlCoq.Ascii (false, false,
                               true, false, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (false,
                                    false, true, false, false, true, b5,
                                    b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (false,
                                         false, true, false, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (false, false, true, false,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (false,
                                                   false, true, false, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (false,
                                                        false, true, false,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (false, false,
                                                             true, false,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_str
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (PubkeyRes
                                                                    p0)))))
              else if b2
                   then if b3
                        then let m = Coq_pair ((MlCoq.Ascii (false, false,
                               false, true, true, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m))))
                        else if b4
                             then let m = Coq_pair ((MlCoq.Ascii (false,
                                    false, false, true, false, true, b5,
                                    b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (false,
                                         false, false, true, false, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (false, false, false, true,
                                              false, false, false, true)),
                                              a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (false,
                                                   false, false, true, false,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (false,
                                                        false, false, true,
                                                        false, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (false, false,
                                                             false, true,
                                                             false, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_fd
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_fd
                                                                    c))
                                                                    (fun p1 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (CreatePtyerRes
                                                                    (p0,
                                                                    p1)))))))
                   else if b3
                        then if b4
                             then let m = Coq_pair ((MlCoq.Ascii (false,
                                    false, false, false, true, true, b5,
                                    b6)), a0)
                                  in
                                  coq_SepWeaken
                                    (coq_SepStrengthen
                                      (coq_SepFrame
                                        (coq_SepReturn (BadTag m))))
                             else if b5
                                  then let m = Coq_pair ((MlCoq.Ascii (false,
                                         false, false, false, true, false,
                                         true, b6)), a0)
                                       in
                                       coq_SepWeaken
                                         (coq_SepStrengthen
                                           (coq_SepFrame
                                             (coq_SepReturn (BadTag m))))
                                  else if b6
                                       then let m = Coq_pair ((MlCoq.Ascii
                                              (false, false, false, false,
                                              true, false, false, true)), a0)
                                            in
                                            coq_SepWeaken
                                              (coq_SepStrengthen
                                                (coq_SepFrame
                                                  (coq_SepReturn (BadTag m))))
                                       else let MlCoq.Ascii
                                              (b7, b8, b9, b10, b11, b12,
                                               b13, b14) = a0
                                            in
                                            if b7
                                            then let m = Coq_pair
                                                   ((MlCoq.Ascii (false,
                                                   false, false, false, true,
                                                   false, false, false)),
                                                   (MlCoq.Ascii (true, b8,
                                                   b9, b10, b11, b12, b13,
                                                   b14)))
                                                 in
                                                 coq_SepWeaken
                                                   (coq_SepStrengthen
                                                     (coq_SepFrame
                                                       (coq_SepReturn (BadTag
                                                         m))))
                                            else if b8
                                                 then let m = Coq_pair
                                                        ((MlCoq.Ascii (false,
                                                        false, false, false,
                                                        true, false, false,
                                                        false)), (MlCoq.Ascii
                                                        (false, true, b9,
                                                        b10, b11, b12, b13,
                                                        b14)))
                                                      in
                                                      coq_SepWeaken
                                                        (coq_SepStrengthen
                                                          (coq_SepFrame
                                                            (coq_SepReturn
                                                              (BadTag m))))
                                                 else if b9
                                                      then let m = Coq_pair
                                                             ((MlCoq.Ascii
                                                             (false, false,
                                                             false, false,
                                                             true, false,
                                                             false, false)),
                                                             (MlCoq.Ascii
                                                             (false, false,
                                                             true, b10, b11,
                                                             b12, b13, b14)))
                                                           in
                                                           coq_SepWeaken
                                                             (coq_SepStrengthen
                                                               (coq_SepFrame
                                                                 (coq_SepReturn
                                                                   (BadTag
                                                                   m))))
                                                      else if b10
                                                           then let m =
                                                                  Coq_pair
                                                                  ((MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  false,
                                                                  true,
                                                                  false,
                                                                  false,
                                                                  false)),
                                                                  (MlCoq.Ascii
                                                                  (false,
                                                                  false,
                                                                  false,
                                                                  true, b11,
                                                                  b12, b13,
                                                                  b14)))
                                                                in
                                                                coq_SepWeaken
                                                                  (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                           else if b11
                                                                then 
                                                                  let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b12, b13,
                                                                    b14)))
                                                                  in
                                                                  coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                else 
                                                                  if b12
                                                                  then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b13,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                  else 
                                                                    if b13
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    b14)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    if b14
                                                                    then 
                                                                    let m =
                                                                    Coq_pair
                                                                    ((MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false)),
                                                                    (MlCoq.Ascii
                                                                    (false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)))
                                                                    in
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (BadTag
                                                                    m))))
                                                                    else 
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_fd
                                                                    c))
                                                                    (fun p0 ->
                                                                    coq_SepBind
                                                                    (coq_SepStrengthen
                                                                    (recv_fd
                                                                    c))
                                                                    (fun p1 ->
                                                                    coq_SepWeaken
                                                                    (coq_SepStrengthen
                                                                    (coq_SepFrame
                                                                    (coq_SepReturn
                                                                    (SysCreatePtyerRes
                                                                    (p0,
                                                                    p1)))))))
                        else let m = Coq_pair ((MlCoq.Ascii (false, false,
                               false, false, false, b4, b5, b6)), a0)
                             in
                             coq_SepWeaken
                               (coq_SepStrengthen
                                 (coq_SepFrame (coq_SepReturn (BadTag m)))))

(** val send_msg : tchan -> msg -> unit coq_STsep **)

let send_msg c = function
| LoginReq p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (true, false, false, false, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| LoginRes p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (false, true, false, false, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_num c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| PubkeyReq ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (true, true, false, false, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ()))))
| PubkeyRes p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (false, false, true, false, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| KeysignReq p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (true, false, true, false, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| KeysignRes p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (false, true, true, false, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| CreatePtyerReq ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (true, true, true, false, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ()))))
| CreatePtyerRes (p0, p1) ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (false, false, false, true, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_fd c p0))
      (coq_SepSeq (coq_SepStrengthen (send_fd c p1))
        (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ()))))))
| SysLoginReq p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (true, false, false, true, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| SysLoginRes (p0, p1) ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (false, true, false, true, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepSeq (coq_SepStrengthen (send_num c p1))
        (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ()))))))
| SysPubkeyReq ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (true, true, false, true, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ()))))
| SysPubkeyRes p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (false, false, true, true, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| SysKeysignReq p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (true, false, true, true, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| SysKeysignRes p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (false, true, true, true, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| SysCreatePtyerReq p0 ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (true, true, true, true, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_str c p0))
      (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ())))))
| SysCreatePtyerRes (p0, p1) ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (false, false, false, false, true,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepSeq (coq_SepStrengthen (send_fd c p0))
      (coq_SepSeq (coq_SepStrengthen (send_fd c p1))
        (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ()))))))
| BadTag n ->
  coq_SepSeq
    (coq_SepStrengthen
      (send_num c (Coq_pair ((MlCoq.Ascii (false, false, false, false, false,
        false, false, false)), (MlCoq.Ascii (false, false, false, false,
        false, false, false, false))))))
    (coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn ()))))

