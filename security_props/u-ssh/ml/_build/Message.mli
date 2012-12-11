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

val num_rect : ((MlCoq.ascii, MlCoq.ascii) prod -> 'a1) -> num -> 'a1

val num_rec : ((MlCoq.ascii, MlCoq.ascii) prod -> 'a1) -> num -> 'a1

val nat_of_num : num -> MlCoq.nat

val num_of_nat : MlCoq.nat -> num

val str_of_string : MlCoq.ascii list -> str

type chan_type =
| System
| Slave

val chan_type_rect : 'a1 -> 'a1 -> chan_type -> 'a1

val chan_type_rec : 'a1 -> 'a1 -> chan_type -> 'a1

val chan_path : chan_type -> str

type chan = KrakenImpl.chan

type st_System =
| Build_st_System

val st_System_rect : 'a1 -> 'a1

val st_System_rec : 'a1 -> 'a1

type st_Slave =
| Build_st_Slave

val st_Slave_rect : 'a1 -> 'a1

val st_Slave_rec : 'a1 -> 'a1

type comp_state = __

type tchan = (chan_type, (chan, comp_state) prod) sigT

val tchan_eq : tchan -> tchan -> bool

type fdesc = KrakenImpl.fdesc

type coq_Action =
| Exec of str * tchan
| Call of str * str * fdesc
| Select of tchan list * tchan
| Recv of tchan * str
| Send of tchan * str
| RecvFD of tchan * fdesc
| SendFD of tchan * fdesc

val coq_Action_rect :
  (str -> tchan -> 'a1) -> (str -> str -> fdesc -> 'a1) -> (tchan list ->
  tchan -> 'a1) -> (tchan -> str -> 'a1) -> (tchan -> str -> 'a1) -> (tchan
  -> fdesc -> 'a1) -> (tchan -> fdesc -> 'a1) -> coq_Action -> 'a1

val coq_Action_rec :
  (str -> tchan -> 'a1) -> (str -> str -> fdesc -> 'a1) -> (tchan list ->
  tchan -> 'a1) -> (tchan -> str -> 'a1) -> (tchan -> str -> 'a1) -> (tchan
  -> fdesc -> 'a1) -> (tchan -> fdesc -> 'a1) -> coq_Action -> 'a1

type coq_Trace = coq_Action list

val exec : chan_type -> str -> comp_state -> tchan coq_STsep

val call : str -> str -> fdesc coq_STsep

val select : tchan list -> tchan coq_STsep

val recv : tchan -> num -> str coq_STsep

val send : tchan -> str -> unit coq_STsep

val recv_fd : tchan -> fdesc coq_STsep

val send_fd : tchan -> fdesc -> unit coq_STsep

val coq_RecvNum : tchan -> num -> coq_Trace

val recv_num : tchan -> num coq_STsep

val coq_SendNum : tchan -> num -> coq_Trace

val send_num : tchan -> num -> unit coq_STsep

val coq_RecvStr : tchan -> str -> coq_Trace

val recv_str : tchan -> str coq_STsep

val coq_SendStr : tchan -> str -> coq_Trace

val send_str : tchan -> str -> unit coq_STsep

val coq_Exec_t : str -> tchan -> coq_Trace

val coq_Call_t : str -> str -> fdesc -> coq_Trace

val coq_RecvFD_t : tchan -> fdesc -> coq_Trace

val coq_SendFD_t : tchan -> fdesc -> coq_Trace

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

val msg_rect :
  (str -> 'a1) -> (num -> 'a1) -> 'a1 -> (str -> 'a1) -> (str -> 'a1) -> (str
  -> 'a1) -> 'a1 -> (fdesc -> fdesc -> 'a1) -> (str -> 'a1) -> (str -> num ->
  'a1) -> 'a1 -> (str -> 'a1) -> (str -> 'a1) -> (str -> 'a1) -> (str -> 'a1)
  -> (fdesc -> fdesc -> 'a1) -> (num -> 'a1) -> msg -> 'a1

val msg_rec :
  (str -> 'a1) -> (num -> 'a1) -> 'a1 -> (str -> 'a1) -> (str -> 'a1) -> (str
  -> 'a1) -> 'a1 -> (fdesc -> fdesc -> 'a1) -> (str -> 'a1) -> (str -> num ->
  'a1) -> 'a1 -> (str -> 'a1) -> (str -> 'a1) -> (str -> 'a1) -> (str -> 'a1)
  -> (fdesc -> fdesc -> 'a1) -> (num -> 'a1) -> msg -> 'a1

val coq_RecvMsg : tchan -> msg -> coq_Trace

val coq_SendMsg : tchan -> msg -> coq_Trace

val recv_msg : tchan -> msg coq_STsep

val send_msg : tchan -> msg -> unit coq_STsep

