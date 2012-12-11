open Datatypes
open Message
open Peano
open Peano_dec
open STsep
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_KAction =
| KExec of str * tchan
| KCall of str * str * fdesc
| KSelect of tchan list * tchan
| KSend of tchan * msg
| KRecv of tchan * msg

(** val coq_KAction_rect :
    (str -> tchan -> 'a1) -> (str -> str -> fdesc -> 'a1) -> (tchan list ->
    tchan -> 'a1) -> (tchan -> msg -> 'a1) -> (tchan -> msg -> 'a1) ->
    coq_KAction -> 'a1 **)

let coq_KAction_rect f f0 f1 f2 f3 = function
| KExec (x, x0) -> f x x0
| KCall (x, x0, x1) -> f0 x x0 x1
| KSelect (x, x0) -> f1 x x0
| KSend (x, x0) -> f2 x x0
| KRecv (x, x0) -> f3 x x0

(** val coq_KAction_rec :
    (str -> tchan -> 'a1) -> (str -> str -> fdesc -> 'a1) -> (tchan list ->
    tchan -> 'a1) -> (tchan -> msg -> 'a1) -> (tchan -> msg -> 'a1) ->
    coq_KAction -> 'a1 **)

let coq_KAction_rec f f0 f1 f2 f3 = function
| KExec (x, x0) -> f x x0
| KCall (x, x0, x1) -> f0 x x0 x1
| KSelect (x, x0) -> f1 x x0
| KSend (x, x0) -> f2 x x0
| KRecv (x, x0) -> f3 x x0

type coq_KTrace = coq_KAction list

(** val expand_kaction : coq_KAction -> coq_Trace **)

let expand_kaction = function
| KExec (cmd, c) -> (Exec (cmd, c))::[]
| KCall (cmd, arg, pipe) -> (Call (cmd, arg, pipe))::[]
| KSelect (cs, c) -> (Select (cs, c))::[]
| KSend (c, m) -> coq_SendMsg c m
| KRecv (c, m) -> coq_RecvMsg c m

(** val expand_ktrace : coq_KTrace -> coq_Trace **)

let rec expand_ktrace = function
| [] -> []
| ka::kas -> app (expand_kaction ka) (expand_ktrace kas)

type kstate = { components : tchan list; system : tchan; slave : tchan;
                logincnt : num; loginsucceded : num; username : str }

(** val kstate_rect :
    (tchan list -> __ -> tchan -> tchan -> num -> num -> str -> 'a1) ->
    kstate -> 'a1 **)

let kstate_rect f k =
  let { components = x; system = x0; slave = x1; logincnt = x2;
    loginsucceded = x3; username = x4 } = k
  in
  f x __ x0 x1 x2 x3 x4

(** val kstate_rec :
    (tchan list -> __ -> tchan -> tchan -> num -> num -> str -> 'a1) ->
    kstate -> 'a1 **)

let kstate_rec f k =
  let { components = x; system = x0; slave = x1; logincnt = x2;
    loginsucceded = x3; username = x4 } = k
  in
  f x __ x0 x1 x2 x3 x4

(** val components : kstate -> tchan list **)

let components x = x.components

(** val system : kstate -> tchan **)

let system x = x.system

(** val slave : kstate -> tchan **)

let slave x = x.slave

(** val logincnt : kstate -> num **)

let logincnt x = x.logincnt

(** val loginsucceded : kstate -> num **)

let loginsucceded x = x.loginsucceded

(** val username : kstate -> str **)

let username x = x.username

(** val kinit : unit -> kstate coq_STsep **)

let kinit h =
  coq_SepBind
    (coq_SepStrengthen
      (coq_SepFrame
        (exec System
          (str_of_string ((MlCoq.Ascii (true, true, false, false, true, true,
            true, false))::((MlCoq.Ascii (true, false, false, true, true,
            true, true, false))::((MlCoq.Ascii (true, true, false, false,
            true, true, true, false))::((MlCoq.Ascii (false, false, true,
            false, true, true, true, false))::((MlCoq.Ascii (true, false,
            true, false, false, true, true, false))::((MlCoq.Ascii (true,
            false, true, true, false, true, true, false))::[])))))))
          (Obj.magic __)))) (fun system_25 ->
    coq_SepBind
      (coq_SepStrengthen
        (coq_SepFrame
          (exec Slave
            (str_of_string ((MlCoq.Ascii (true, true, false, false, true,
              true, true, false))::((MlCoq.Ascii (false, false, true, true,
              false, true, true, false))::((MlCoq.Ascii (true, false, false,
              false, false, true, true, false))::((MlCoq.Ascii (false, true,
              true, false, true, true, true, false))::((MlCoq.Ascii (true,
              false, true, false, false, true, true, false))::[]))))))
            (Obj.magic __)))) (fun slave_26 ->
      coq_SepWeaken
        (coq_SepStrengthen
          (coq_SepFrame
            (coq_SepReturn { components = (slave_26::(system_25::[]));
              system = system_25; slave = slave_26; logincnt = (Coq_pair
              ((MlCoq.Ascii (false, false, false, false, false, false, false,
              false)), (MlCoq.Ascii (false, false, false, false, false,
              false, false, false)))); loginsucceded = (Coq_pair
              ((MlCoq.Ascii (false, false, false, false, false, false, false,
              false)), (MlCoq.Ascii (false, false, false, false, false,
              false, false, false)))); username = (str_of_string []) })))))

(** val exchange_System : tchan -> kstate -> kstate coq_STsep **)

let exchange_System c kst =
  let comps = kst.components in
  let system0 = kst.system in
  let slave0 = kst.slave in
  let logincnt0 = kst.logincnt in
  let loginsucceded0 = kst.loginsucceded in
  let username0 = kst.username in
  coq_SepBind (coq_SepStrengthen (coq_SepFrame (recv_msg c))) (fun req ->
    match req with
    | SysLoginRes (autheduser, resnum) ->
      coq_SepSeq
        (coq_SepStrengthen
          (coq_SepFrame (send_msg slave0 (LoginRes resnum))))
        (coq_SepWeaken
          (coq_SepStrengthen
            (coq_SepFrame
              (coq_SepReturn { components = comps; system = system0; slave =
                slave0; logincnt = logincnt0; loginsucceded = resnum;
                username = autheduser }))))
    | SysPubkeyRes pubkeystr ->
      coq_SepSeq
        (coq_SepStrengthen
          (coq_SepFrame (send_msg slave0 (PubkeyRes pubkeystr))))
        (coq_SepWeaken
          (coq_SepStrengthen
            (coq_SepFrame
              (coq_SepReturn { components = comps; system = system0; slave =
                slave0; logincnt = logincnt0; loginsucceded = loginsucceded0;
                username = username0 }))))
    | SysKeysignRes signedkey ->
      coq_SepSeq
        (coq_SepStrengthen
          (coq_SepFrame (send_msg slave0 (KeysignRes signedkey))))
        (coq_SepWeaken
          (coq_SepStrengthen
            (coq_SepFrame
              (coq_SepReturn { components = comps; system = system0; slave =
                slave0; logincnt = logincnt0; loginsucceded = loginsucceded0;
                username = username0 }))))
    | SysCreatePtyerRes (slavefd, masterfd) ->
      coq_SepSeq
        (coq_SepStrengthen
          (coq_SepFrame
            (send_msg slave0 (CreatePtyerRes (slavefd, masterfd)))))
        (coq_SepWeaken
          (coq_SepStrengthen
            (coq_SepFrame
              (coq_SepReturn { components = comps; system = system0; slave =
                slave0; logincnt = logincnt0; loginsucceded = loginsucceded0;
                username = username0 }))))
    | _ ->
      coq_SepWeaken
        (coq_SepStrengthen
          (coq_SepFrame
            (coq_SepReturn { components = comps; system = system0; slave =
              slave0; logincnt = logincnt0; loginsucceded = loginsucceded0;
              username = username0 }))))

(** val exchange_Slave : tchan -> kstate -> kstate coq_STsep **)

let exchange_Slave c kst =
  let comps = kst.components in
  let system0 = kst.system in
  let slave0 = kst.slave in
  let logincnt0 = kst.logincnt in
  let loginsucceded0 = kst.loginsucceded in
  let username0 = kst.username in
  coq_SepBind (coq_SepStrengthen (coq_SepFrame (recv_msg c))) (fun req ->
    match req with
    | LoginReq accstr ->
      if eq_nat_dec (nat_of_num logincnt0) (MlCoq.S (MlCoq.S (MlCoq.S
           MlCoq.O)))
      then coq_SepWeaken
             (coq_SepStrengthen
               (coq_SepFrame
                 (coq_SepReturn { components = comps; system = system0;
                   slave = slave0; logincnt = logincnt0; loginsucceded =
                   loginsucceded0; username = username0 })))
      else coq_SepSeq
             (coq_SepStrengthen
               (coq_SepFrame (send_msg system0 (SysLoginReq accstr))))
             (coq_SepWeaken
               (coq_SepStrengthen
                 (coq_SepFrame
                   (coq_SepReturn { components = comps; system = system0;
                     slave = slave0; logincnt =
                     (num_of_nat
                       (plus (nat_of_num logincnt0)
                         (nat_of_num (Coq_pair ((MlCoq.Ascii (true, false,
                           false, false, false, false, false, false)),
                           (MlCoq.Ascii (false, false, false, false, false,
                           false, false, false))))))); loginsucceded =
                     loginsucceded0; username = username0 }))))
    | PubkeyReq ->
      coq_SepSeq
        (coq_SepStrengthen (coq_SepFrame (send_msg system0 SysPubkeyReq)))
        (coq_SepWeaken
          (coq_SepStrengthen
            (coq_SepFrame
              (coq_SepReturn { components = comps; system = system0; slave =
                slave0; logincnt = logincnt0; loginsucceded = loginsucceded0;
                username = username0 }))))
    | KeysignReq datastr ->
      coq_SepSeq
        (coq_SepStrengthen
          (coq_SepFrame (send_msg system0 (SysKeysignReq datastr))))
        (coq_SepWeaken
          (coq_SepStrengthen
            (coq_SepFrame
              (coq_SepReturn { components = comps; system = system0; slave =
                slave0; logincnt = logincnt0; loginsucceded = loginsucceded0;
                username = username0 }))))
    | CreatePtyerReq ->
      if eq_nat_dec (nat_of_num loginsucceded0) MlCoq.O
      then coq_SepWeaken
             (coq_SepStrengthen
               (coq_SepFrame
                 (coq_SepReturn { components = comps; system = system0;
                   slave = slave0; logincnt = logincnt0; loginsucceded =
                   loginsucceded0; username = username0 })))
      else coq_SepSeq
             (coq_SepStrengthen
               (coq_SepFrame
                 (send_msg system0 (SysCreatePtyerReq username0))))
             (coq_SepWeaken
               (coq_SepStrengthen
                 (coq_SepFrame
                   (coq_SepReturn { components = comps; system = system0;
                     slave = slave0; logincnt = logincnt0; loginsucceded =
                     loginsucceded0; username = username0 }))))
    | _ ->
      coq_SepWeaken
        (coq_SepStrengthen
          (coq_SepFrame
            (coq_SepReturn { components = comps; system = system0; slave =
              slave0; logincnt = logincnt0; loginsucceded = loginsucceded0;
              username = username0 }))))

(** val type_of_comp : tchan -> tchan list -> chan_type **)

let rec type_of_comp c = function
| [] -> System
| x::rest -> if tchan_eq x c then projT1 x else type_of_comp c rest

(** val kbody : kstate -> kstate coq_STsep **)

let kbody kst =
  let comps = kst.components in
  let system0 = kst.system in
  let slave0 = kst.slave in
  let logincnt0 = kst.logincnt in
  let loginsucceded0 = kst.loginsucceded in
  let username0 = kst.username in
  coq_SepBind (coq_SepStrengthen (coq_SepFrame (select comps))) (fun comp ->
    let handler =
      let p = projT1 comp in
      (fun _ ->
      match p with
      | System -> exchange_System comp
      | Slave -> exchange_Slave comp)
    in
    coq_SepBind
      (coq_SepStrengthen
        (handler __ { components = comps; system = system0; slave = slave0;
          logincnt = logincnt0; loginsucceded = loginsucceded0; username =
          username0 })) (fun s' ->
      coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn s')))))

(** val kloop : kstate -> kstate coq_STsep **)

let kloop s =
  coq_SepFix (fun self s0 ->
    coq_SepBind (coq_SepStrengthen (kbody s0)) (fun s1 ->
      coq_SepBind (coq_SepStrengthen (self s1)) (fun s2 ->
        coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn s2))))))
    s

(** val main : unit -> kstate coq_STsep **)

let main h =
  coq_SepBind (coq_SepStrengthen (kinit ())) (fun s0 ->
    coq_SepBind (coq_SepStrengthen (kloop s0)) (fun sN ->
      coq_SepWeaken (coq_SepStrengthen (coq_SepFrame (coq_SepReturn sN)))))

