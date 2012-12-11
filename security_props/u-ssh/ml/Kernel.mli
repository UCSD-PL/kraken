open Datatypes
open Message
open Peano
open Peano_dec
open STsep
open Specif

type __ = Obj.t

type coq_KAction =
| KExec of str * tchan
| KCall of str * str * fdesc
| KSelect of tchan list * tchan
| KSend of tchan * msg
| KRecv of tchan * msg

val coq_KAction_rect :
  (str -> tchan -> 'a1) -> (str -> str -> fdesc -> 'a1) -> (tchan list ->
  tchan -> 'a1) -> (tchan -> msg -> 'a1) -> (tchan -> msg -> 'a1) ->
  coq_KAction -> 'a1

val coq_KAction_rec :
  (str -> tchan -> 'a1) -> (str -> str -> fdesc -> 'a1) -> (tchan list ->
  tchan -> 'a1) -> (tchan -> msg -> 'a1) -> (tchan -> msg -> 'a1) ->
  coq_KAction -> 'a1

type coq_KTrace = coq_KAction list

val expand_kaction : coq_KAction -> coq_Trace

val expand_ktrace : coq_KTrace -> coq_Trace

type kstate = { components : tchan list; system : tchan; slave : tchan;
                logincnt : num; loginsucceded : num; username : str }

val kstate_rect :
  (tchan list -> __ -> tchan -> tchan -> num -> num -> str -> 'a1) -> kstate
  -> 'a1

val kstate_rec :
  (tchan list -> __ -> tchan -> tchan -> num -> num -> str -> 'a1) -> kstate
  -> 'a1

val components : kstate -> tchan list

val system : kstate -> tchan

val slave : kstate -> tchan

val logincnt : kstate -> num

val loginsucceded : kstate -> num

val username : kstate -> str

val kinit : unit -> kstate coq_STsep

val exchange_System : tchan -> kstate -> kstate coq_STsep

val exchange_Slave : tchan -> kstate -> kstate coq_STsep

val type_of_comp : tchan -> tchan list -> chan_type

val kbody : kstate -> kstate coq_STsep

val kloop : kstate -> kstate coq_STsep

val main : unit -> kstate coq_STsep

