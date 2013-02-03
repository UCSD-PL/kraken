Require Import Regex.
Require Import Reflex.
Require Import ReflexFin.
Require Import ReflexBase.
Require Import Ynot.

(*Two message types: auth response and open pty*)
Definition SSH_NB_MSG := 2.

(*Auth response has the username and a num indicating success*)
Definition msg_d_authres : payload_desc :=
  existT _ 2 (str_d, (num_d, tt)).
Definition authres_num : fin SSH_NB_MSG := None.

(*Open pty has the username*)
Definition msg_d_openpty : payload_desc :=
  existT _ 1 (str_d, tt).
Definition openpty_num : fin SSH_NB_MSG := Some None.

Definition SSH_TBL := (msg_d_authres, (msg_d_openpty, tt)).

Record kstate_t {NB_MSG : nat} {PDV : payload_desc_vec NB_MSG} : Set := mkst_t
  { components : list fd
    ; ktr : inhabited (Reflex.KTrace NB_MSG PDV)
    ; system : fd
    ; slave : fd
    ; logincnt : num
    ; loginsucceded : num
    ; username : str}.

Inductive ValidExchange :
  (@kstate_t SSH_NB_MSG SSH_TBL) ->
  (@kstate_t SSH_NB_MSG SSH_TBL) -> Prop :=
| VE_OpenPtyerSend : forall st slv,
    nat_of_num (loginsucceded st) = 1 ->
    let tr := (ktr st) in
    ValidExchange st
      (mkst_t _ _
         (components st)
         (tr ~~~ KSend _ _ slv
             (Build_msg SSH_NB_MSG SSH_TBL openpty_num
                        (username st, tt))::tr)
         (system st)
         (slave st)
         (logincnt st)
         (loginsucceded st)
         (username st))
| VE_AuthRes : forall st sys user resnum,
   let tr := (ktr st) in
   ValidExchange st
     (mkst_t _ _
        (components st)
        (tr ~~~ KRecv _ _ sys
            (Build_msg SSH_NB_MSG SSH_TBL authres_num
                       (user, (resnum, tt)))::tr)
        sys
        (slave st)
        (logincnt st)
        resnum
        user).

Inductive KInvariant : (@kstate_t SSH_NB_MSG SSH_TBL) -> Prop :=
| KI_init : forall slv sys,
    KInvariant
      (mkst_t _ _
         (sys::slv::nil)
         [nil]%inhabited
         sys
         slv
         (num_of_nat 0)
         (num_of_nat 0)
         (str_of_string ""))
| KI_exchange : forall s s',
    KInvariant s ->
    ValidExchange s s' ->
    KInvariant s'.

Definition RE_Auth_PTY user res : Regexp :=
  RE_Alt
    (RE_Star
       (RE_NAtom
          (@KOSend SSH_NB_MSG SSH_TBL None
                  (@Build_opt_msg SSH_NB_MSG SSH_TBL
                                  openpty_num
                                  (Some user, tt)))))
    (RE_Concat
       (RE_Star RE_Any)
       (RE_Concat (RE_Atom
                     (@KORecv SSH_NB_MSG SSH_TBL None
                             (@Build_opt_msg SSH_NB_MSG SSH_TBL
                                             authres_num
                                             (Some user, (Some res, tt)))))
                  (RE_NAtom
                     (@KOSend SSH_NB_MSG SSH_TBL None
                             (@Build_opt_msg SSH_NB_MSG SSH_TBL
                                             openpty_num
                                             (Some user, tt)))))).


(*This theorem is sort of cheating. It assumes that a successful response
  is a 1. In the old version of the SSH server, a successful response
  was any non-zero value. You have to start somewhere.*)
Theorem priv_auth : forall st tr user,
  KInvariant st -> inhabits tr = ktr st ->
  RMatch (RE_Auth_PTY user (num_of_nat 1)) tr.
