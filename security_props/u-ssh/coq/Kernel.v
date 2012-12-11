Require Import Ascii.
Require Import List.
Require Import String.
Require Import Ynot.
Require Import Message.

Open Local Scope char_scope.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Fixpoint all_bound (cs : list tchan) : hprop :=
  match cs with
    | nil => emp
    | c :: cs' => bound c * all_bound cs'
  end.

Fixpoint all_bound_drop (cs : list tchan) (drop : tchan) : hprop :=
  match cs with
  | nil => emp
  | c :: cs' =>
    if tchan_eq c drop
      then all_bound cs'
      else bound c * all_bound_drop cs' drop
  end.

Lemma unpack_all_bound :
  forall cs c,
  In c cs ->
  all_bound cs ==> bound c * all_bound_drop cs c.
Proof.
  induction cs; simpl; intros. contradiction.
  destruct H; subst. rewrite tchan_eq_true. apply himp_refl.
  case (tchan_eq a c); intros; subst. apply himp_refl.
  apply himp_comm_conc. apply himp_assoc_conc1.
  apply himp_split. apply himp_refl.
  apply himp_comm_conc; auto.
Qed.

Lemma repack_all_bound :
  forall cs c,
  In c cs ->
  bound c * all_bound_drop cs c ==> all_bound cs.
Proof.
  induction cs; simpl; intros. contradiction.
  destruct H; subst. rewrite tchan_eq_true. apply himp_refl.
  case (tchan_eq a c); intros; subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.

Ltac sep' := sep fail idtac.

Ltac isolate t :=
  match t with ?lhs ==> ?rhs =>
    refine (@himp_trans (lhs * _) _ _ _ _); [ sep' | ];
    refine (@himp_trans (rhs * _) _ _ _ _); [ | sep' ];
    apply himp_split
  end.

Ltac bounds_packing :=
  match goal with
  | [ |- ?lhs ==> ?rhs ] =>
    match lhs with context [ all_bound_drop ?cs ?c ] =>
      isolate (bound c * all_bound_drop cs c ==> all_bound cs);
      [ apply repack_all_bound | ]
    end

  | [ |- ?lhs ==> ?rhs ] =>
    match rhs with context [ all_bound_drop ?cs ?c ] =>
      isolate (all_bound cs ==> bound c * all_bound_drop cs c);
      [ apply unpack_all_bound | ]
    end

  | [ |- ?lhs ==> ?rhs ] =>
    match lhs with context [ all_bound_drop ?cs ?c ] =>
    match rhs with context [ all_bound_drop ?cs ?d ] =>
      isolate (bound c * all_bound_drop cs c ==> bound d * all_bound_drop cs d);
      [ eapply himp_trans; [ apply repack_all_bound | apply unpack_all_bound ] | ]
    end
    end
end.

Inductive KAction : Set :=
| KExec   : str -> tchan -> KAction
| KCall   : str -> str -> fdesc -> KAction
| KSelect : list tchan -> tchan -> KAction
| KSend   : tchan -> msg -> KAction
| KRecv   : tchan -> msg -> KAction
.

Definition KTrace : Set :=
  list KAction.

Definition expand_kaction (ka : KAction) : Trace :=
  match ka with
  | KExec cmd c => Exec cmd c :: nil
  | KCall cmd arg pipe => Call cmd arg pipe :: nil
  | KSelect cs c => Select cs c :: nil
  | KSend c m => SendMsg c m
  | KRecv c m => RecvMsg c m
  end.

Fixpoint expand_ktrace (kt : KTrace) : Trace :=
  match kt with
  | nil => nil
  | ka :: kas => expand_kaction ka ++ expand_ktrace kas
  end.

Record kstate : Set :=
  mkst { components : list tchan
       ; ktr : [KTrace]
; system : tchan
; slave : tchan
; logincnt : num
; loginsucceded : num
; username : str
       }.

Section VEX.

Variable s : kstate.

Let comps := components s.
Let tr := ktr s.
Let system := system s.

Let slave := slave s.

Let logincnt := logincnt s.

Let loginsucceded := loginsucceded s.

Let username := username s.


Inductive ValidExchange : kstate -> Prop :=
| VE_System_SysLoginRes_0 :
forall autheduser c resnum (CT : projT1 c = System),
True ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KSend slave (LoginRes (resnum)) :: KRecv c (SysLoginRes autheduser resnum) :: tr)
  (system)
(slave)
(logincnt)
(resnum)
(autheduser)
)
| VE_System_SysPubkeyRes_0 :
forall c pubkeystr (CT : projT1 c = System),
True ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KSend slave (PubkeyRes (pubkeystr)) :: KRecv c (SysPubkeyRes pubkeystr) :: tr)
  (system)
(slave)
(logincnt)
(loginsucceded)
(username)
)
| VE_System_SysKeysignRes_0 :
forall c signedkey (CT : projT1 c = System),
True ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KSend slave (KeysignRes (signedkey)) :: KRecv c (SysKeysignRes signedkey) :: tr)
  (system)
(slave)
(logincnt)
(loginsucceded)
(username)
)
| VE_System_SysCreatePtyerRes_0 :
forall c masterfd slavefd (CT : projT1 c = System),
True ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KSend slave (CreatePtyerRes (slavefd) (masterfd)) :: KRecv c (SysCreatePtyerRes slavefd masterfd) :: tr)
  (system)
(slave)
(logincnt)
(loginsucceded)
(username)
)
| VE_Slave_LoginReq_1 :
forall accstr c (CT : projT1 c = Slave),
~ (nat_of_num logincnt = 3) -> True ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KSend system (SysLoginReq (accstr)) :: KRecv c (LoginReq accstr) :: tr)
  (system)
(slave)
((num_of_nat ((nat_of_num (logincnt)) + (nat_of_num ((Num ("001", "000")))))))
(loginsucceded)
(username)
)
| VE_Slave_LoginReq_0 :
forall accstr c (CT : projT1 c = Slave),
(nat_of_num logincnt = 3) ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KRecv c (LoginReq accstr) :: tr)
  (system)
(slave)
(logincnt)
(loginsucceded)
(username)
)
| VE_Slave_PubkeyReq_0 :
forall c (CT : projT1 c = Slave),
True ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KSend system (SysPubkeyReq) :: KRecv c (PubkeyReq ) :: tr)
  (system)
(slave)
(logincnt)
(loginsucceded)
(username)
)
| VE_Slave_KeysignReq_0 :
forall c datastr (CT : projT1 c = Slave),
True ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KSend system (SysKeysignReq (datastr)) :: KRecv c (KeysignReq datastr) :: tr)
  (system)
(slave)
(logincnt)
(loginsucceded)
(username)
)
| VE_Slave_CreatePtyerReq_1 :
forall c (CT : projT1 c = Slave),
~ (nat_of_num loginsucceded = 0) -> True ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KSend system (SysCreatePtyerReq (username)) :: KRecv c (CreatePtyerReq ) :: tr)
  (system)
(slave)
(logincnt)
(loginsucceded)
(username)
)
| VE_Slave_CreatePtyerReq_0 :
forall c (CT : projT1 c = Slave),
(nat_of_num loginsucceded = 0) ->
ValidExchange (mkst
  (comps)
  (tr ~~~ KRecv c (CreatePtyerReq ) :: tr)
  (system)
(slave)
(logincnt)
(loginsucceded)
(username)
)
| VE_System_LoginReq:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (LoginReq str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_LoginRes:
  forall num_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (LoginRes num_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_PubkeyReq:
  forall  c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (PubkeyReq ) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_PubkeyRes:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (PubkeyRes str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_KeysignReq:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (KeysignReq str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_KeysignRes:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (KeysignRes str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_CreatePtyerReq:
  forall  c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (CreatePtyerReq ) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_CreatePtyerRes:
  forall fdesc_0 fdesc_1 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (CreatePtyerRes fdesc_0 fdesc_1) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_SysLoginReq:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysLoginReq str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_SysPubkeyReq:
  forall  c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysPubkeyReq ) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_SysKeysignReq:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysKeysignReq str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_System_SysCreatePtyerReq:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysCreatePtyerReq str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_LoginRes:
  forall num_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (LoginRes num_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_PubkeyRes:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (PubkeyRes str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_KeysignRes:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (KeysignRes str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_CreatePtyerRes:
  forall fdesc_0 fdesc_1 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (CreatePtyerRes fdesc_0 fdesc_1) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_SysLoginReq:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysLoginReq str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_SysLoginRes:
  forall str_0 num_1 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysLoginRes str_0 num_1) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_SysPubkeyReq:
  forall  c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysPubkeyReq ) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_SysPubkeyRes:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysPubkeyRes str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_SysKeysignReq:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysKeysignReq str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_SysKeysignRes:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysKeysignRes str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_SysCreatePtyerReq:
  forall str_0 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysCreatePtyerReq str_0) :: tr)
system
slave
logincnt
loginsucceded
username
  )
| VE_Slave_SysCreatePtyerRes:
  forall fdesc_0 fdesc_1 c,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (SysCreatePtyerRes fdesc_0 fdesc_1) :: tr)
system
slave
logincnt
loginsucceded
username
  )
(* special case for errors *)
| VE_BadTag :
  forall c tag,
  ValidExchange (mkst
    comps
    (tr ~~~ KRecv c (BadTag tag) :: tr)
system 
slave 
logincnt 
loginsucceded 
username 
  ).
End VEX.

Hint Constructors ValidExchange.

Ltac ve_solve_tac :=
  solve
    [ eapply VE_BadTag; eauto
    | eapply VE_System_LoginReq; eauto
    | eapply VE_System_LoginRes; eauto
    | eapply VE_System_PubkeyReq; eauto
    | eapply VE_System_PubkeyRes; eauto
    | eapply VE_System_KeysignReq; eauto
    | eapply VE_System_KeysignRes; eauto
    | eapply VE_System_CreatePtyerReq; eauto
    | eapply VE_System_CreatePtyerRes; eauto
    | eapply VE_System_SysLoginReq; eauto
    | eapply VE_System_SysLoginRes_0; eauto
    | eapply VE_System_SysPubkeyReq; eauto
    | eapply VE_System_SysPubkeyRes_0; eauto
    | eapply VE_System_SysKeysignReq; eauto
    | eapply VE_System_SysKeysignRes_0; eauto
    | eapply VE_System_SysCreatePtyerReq; eauto
    | eapply VE_System_SysCreatePtyerRes_0; eauto
    | eapply VE_Slave_LoginReq_0; eauto
    | eapply VE_Slave_LoginReq_1; eauto
    | eapply VE_Slave_LoginRes; eauto
    | eapply VE_Slave_PubkeyReq_0; eauto
    | eapply VE_Slave_PubkeyRes; eauto
    | eapply VE_Slave_KeysignReq_0; eauto
    | eapply VE_Slave_KeysignRes; eauto
    | eapply VE_Slave_CreatePtyerReq_0; eauto
    | eapply VE_Slave_CreatePtyerReq_1; eauto
    | eapply VE_Slave_CreatePtyerRes; eauto
    | eapply VE_Slave_SysLoginReq; eauto
    | eapply VE_Slave_SysLoginRes; eauto
    | eapply VE_Slave_SysPubkeyReq; eauto
    | eapply VE_Slave_SysPubkeyRes; eauto
    | eapply VE_Slave_SysKeysignReq; eauto
    | eapply VE_Slave_SysKeysignRes; eauto
    | eapply VE_Slave_SysCreatePtyerReq; eauto
    | eapply VE_Slave_SysCreatePtyerRes; eauto
    ].

Inductive KInvariant : kstate -> Prop :=
| KI_init :
forall slave_28 system_27,
KInvariant (mkst (slave_28 :: system_27 :: nil) [KExec (str_of_string "slave") slave_28 :: KExec (str_of_string "system") system_27 :: nil] (system_27)
(slave_28)
((Num ("000", "000")))
((Num ("000", "000")))
((str_of_string "")))
| KI_select :
  forall s cs c,
  let comps := components s in
  let tr := ktr s in
let system := system s in

let slave := slave s in

let logincnt := logincnt s in

let loginsucceded := loginsucceded s in

let username := username s in

  KInvariant s ->
  KInvariant (mkst
    comps
    (tr ~~~ KSelect cs c :: tr)
system 
slave 
logincnt 
loginsucceded 
username 
  )
| KI_exchange :
  forall s s',
  KInvariant s ->
  ValidExchange s s' ->
  KInvariant s'.

Hint Constructors KInvariant.

(* Support replacing a term deep in a list.
 * If target is [FOO] and l is [A :: B :: C :: FOO], then
 * [dangle_from target l] will yield [fun x => A :: B :: C :: x].
 *)
Ltac dangle_from target l :=
  match l with
  | target =>
      constr:(fun (x: KTrace) => x)
  | ?h :: ?t =>
      let dt := dangle_from target t in
      constr:(fun x => h :: dt x)
  end.

Ltac restore_kinv :=
  unfold KTrace in *;
  match goal with
  | [H : ktr ?kst = [?x]%inhabited |- ValidExchange ?kst ?kst'] =>
      let itr := eval simpl in (ktr kst') in
      match itr with [?tr]%inhabited =>
        let dtr := dangle_from x tr in
        replace itr with (inhabit_unpack (ktr kst) dtr);
          [ ve_solve_tac
          | rewrite H; auto
          ]
      end

  | [ H: ktr ?kst = [?x]%inhabited |- KInvariant ?kst' ] =>
    match kst' with context [[?kact :: x]%inhabited] =>
      replace ([kact :: x]%inhabited)
      with (inhabit_unpack (ktr kst) (fun oldktr : KTrace => kact :: oldktr));
        [ eapply KI_select; eauto
        | rewrite H; auto
        ]
    end

  | [_: KInvariant _ |- KInvariant _ ] =>
      econstructor; [eauto|]

  | [H: _ = [_]%inhabited |- _] =>
      rewrite H in *; simpl in *

  | [H:[_]%inhabited = [_]%inhabited |- _] =>
      apply pack_injective in H;
      rewrite -> H in * || rewrite <- H in *
end.

Definition kstate_inv s : hprop :=
  tr :~~ ktr s in emp
  * traced (expand_ktrace tr)
  * [KInvariant s]
  * all_bound (components s)
  * [In (system s) (components s)]
* [In (slave s) (components s)].

Ltac unfoldr :=
  unfold kstate_inv, KTrace in *.

Ltac simplr :=
  sep';
  try bounds_packing;
  try restore_kinv.

Definition kinit :
  forall (_ : unit),
  STsep (traced nil)
        (fun s => kstate_inv s).
Proof.
  intros; refine (
let tr := inhabits nil in

system_25 <- exec System (str_of_string "system") (Build_st_System )
(tr ~~~ expand_ktrace (tr))
<@> emp;

slave_26 <- exec Slave (str_of_string "slave") (Build_st_Slave )
(tr ~~~ expand_ktrace (KExec (str_of_string "system") system_25 :: tr))
<@> bound system_25 * emp;

(* Nop *)

{{ Return (mkst (slave_26 :: system_25 :: nil) (tr ~~~ KExec (str_of_string "slave") slave_26 :: KExec (str_of_string "system") system_25 :: tr) (system_25)
(slave_26)
((Num ("000", "000")))
((Num ("000", "000")))
((str_of_string ""))) }}
  );
  sep unfoldr simplr.
Qed.

Definition exchange_System :
  forall (c : tchan) (CT : projT1 c = System) (kst : kstate),
  STsep (kstate_inv kst * [In c (components kst)])
        (fun (kst' : kstate) => kstate_inv kst').
Proof.
  intros c CT kst;
  pose (comps := components kst);
  pose (tr := ktr kst);
pose (system := system kst);
pose (slave := slave kst);
pose (logincnt := logincnt kst);
pose (loginsucceded := loginsucceded kst);
pose (username := username kst);
  refine (
    req <- recv_msg c
    (tr ~~~ expand_ktrace tr)
    <@> [In c comps] * [In system comps] * [In slave comps] * emp * all_bound_drop comps c * (tr ~~ [KInvariant kst]);
    match req with
| LoginReq __dummy_1__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (LoginReq __dummy_1__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| LoginRes __dummy_2__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (LoginRes __dummy_2__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| PubkeyReq  =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (PubkeyReq ) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| PubkeyRes __dummy_3__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (PubkeyRes __dummy_3__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| KeysignReq __dummy_4__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (KeysignReq __dummy_4__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| KeysignRes __dummy_5__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (KeysignRes __dummy_5__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| CreatePtyerReq  =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (CreatePtyerReq ) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| CreatePtyerRes __dummy_6__ __dummy_7__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (CreatePtyerRes __dummy_6__ __dummy_7__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysLoginReq __dummy_8__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysLoginReq __dummy_8__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysLoginRes autheduser resnum =>
 (

send_msg slave (LoginRes (resnum))
(tr ~~~ expand_ktrace (KRecv c (SysLoginRes autheduser resnum) :: tr))
<@> [In system comps] * [In slave comps] * all_bound_drop comps slave * [In c comps] * (tr ~~ [KInvariant kst]) * emp;;

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KSend slave (LoginRes (resnum)) :: KRecv c (SysLoginRes autheduser resnum) :: tr) (system)
(slave)
(logincnt)
(resnum)
(autheduser)) }}
 ) 
| SysPubkeyReq  =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysPubkeyReq ) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysPubkeyRes pubkeystr =>
 (

send_msg slave (PubkeyRes (pubkeystr))
(tr ~~~ expand_ktrace (KRecv c (SysPubkeyRes pubkeystr) :: tr))
<@> [In system comps] * [In slave comps] * all_bound_drop comps slave * [In c comps] * (tr ~~ [KInvariant kst]) * emp;;

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KSend slave (PubkeyRes (pubkeystr)) :: KRecv c (SysPubkeyRes pubkeystr) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysKeysignReq __dummy_9__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysKeysignReq __dummy_9__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysKeysignRes signedkey =>
 (

send_msg slave (KeysignRes (signedkey))
(tr ~~~ expand_ktrace (KRecv c (SysKeysignRes signedkey) :: tr))
<@> [In system comps] * [In slave comps] * all_bound_drop comps slave * [In c comps] * (tr ~~ [KInvariant kst]) * emp;;

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KSend slave (KeysignRes (signedkey)) :: KRecv c (SysKeysignRes signedkey) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysCreatePtyerReq __dummy_10__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysCreatePtyerReq __dummy_10__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysCreatePtyerRes slavefd masterfd =>
 (

send_msg slave (CreatePtyerRes (slavefd) (masterfd))
(tr ~~~ expand_ktrace (KRecv c (SysCreatePtyerRes slavefd masterfd) :: tr))
<@> [In system comps] * [In slave comps] * all_bound_drop comps slave * [In c comps] * (tr ~~ [KInvariant kst]) * emp;;

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KSend slave (CreatePtyerRes (slavefd) (masterfd)) :: KRecv c (SysCreatePtyerRes slavefd masterfd) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
    (* special case for errors *)
    | BadTag tag =>
      {{ Return (mkst comps (tr ~~~ KRecv c (BadTag tag) :: tr) system slave logincnt loginsucceded username) }}
    end
  );  sep unfoldr simplr.
Qed.
Definition exchange_Slave :
  forall (c : tchan) (CT : projT1 c = Slave) (kst : kstate),
  STsep (kstate_inv kst * [In c (components kst)])
        (fun (kst' : kstate) => kstate_inv kst').
Proof.
  intros c CT kst;
  pose (comps := components kst);
  pose (tr := ktr kst);
pose (system := system kst);
pose (slave := slave kst);
pose (logincnt := logincnt kst);
pose (loginsucceded := loginsucceded kst);
pose (username := username kst);
  refine (
    req <- recv_msg c
    (tr ~~~ expand_ktrace tr)
    <@> [In c comps] * [In system comps] * [In slave comps] * emp * all_bound_drop comps c * (tr ~~ [KInvariant kst]);
    match req with
| LoginReq accstr =>
if (Peano_dec.eq_nat_dec (nat_of_num logincnt) 3) then  (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (LoginReq accstr) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
 else  (

send_msg system (SysLoginReq (accstr))
(tr ~~~ expand_ktrace (KRecv c (LoginReq accstr) :: tr))
<@> [In system comps] * [In slave comps] * all_bound_drop comps system * [In c comps] * (tr ~~ [KInvariant kst]) * emp;;

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KSend system (SysLoginReq (accstr)) :: KRecv c (LoginReq accstr) :: tr) (system)
(slave)
((num_of_nat ((nat_of_num (logincnt)) + (nat_of_num ((Num ("001", "000")))))))
(loginsucceded)
(username)) }}
 ) 
| LoginRes __dummy_11__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (LoginRes __dummy_11__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| PubkeyReq  =>
 (

send_msg system (SysPubkeyReq)
(tr ~~~ expand_ktrace (KRecv c (PubkeyReq ) :: tr))
<@> [In system comps] * [In slave comps] * all_bound_drop comps system * [In c comps] * (tr ~~ [KInvariant kst]) * emp;;

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KSend system (SysPubkeyReq) :: KRecv c (PubkeyReq ) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| PubkeyRes __dummy_12__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (PubkeyRes __dummy_12__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| KeysignReq datastr =>
 (

send_msg system (SysKeysignReq (datastr))
(tr ~~~ expand_ktrace (KRecv c (KeysignReq datastr) :: tr))
<@> [In system comps] * [In slave comps] * all_bound_drop comps system * [In c comps] * (tr ~~ [KInvariant kst]) * emp;;

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KSend system (SysKeysignReq (datastr)) :: KRecv c (KeysignReq datastr) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| KeysignRes __dummy_13__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (KeysignRes __dummy_13__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| CreatePtyerReq  =>
if (Peano_dec.eq_nat_dec (nat_of_num loginsucceded) 0) then  (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (CreatePtyerReq ) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
 else  (

send_msg system (SysCreatePtyerReq (username))
(tr ~~~ expand_ktrace (KRecv c (CreatePtyerReq ) :: tr))
<@> [In system comps] * [In slave comps] * all_bound_drop comps system * [In c comps] * (tr ~~ [KInvariant kst]) * emp;;

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KSend system (SysCreatePtyerReq (username)) :: KRecv c (CreatePtyerReq ) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| CreatePtyerRes __dummy_14__ __dummy_15__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (CreatePtyerRes __dummy_14__ __dummy_15__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysLoginReq __dummy_16__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysLoginReq __dummy_16__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysLoginRes __dummy_17__ __dummy_18__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysLoginRes __dummy_17__ __dummy_18__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysPubkeyReq  =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysPubkeyReq ) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysPubkeyRes __dummy_19__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysPubkeyRes __dummy_19__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysKeysignReq __dummy_20__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysKeysignReq __dummy_20__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysKeysignRes __dummy_21__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysKeysignRes __dummy_21__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysCreatePtyerReq __dummy_22__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysCreatePtyerReq __dummy_22__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
| SysCreatePtyerRes __dummy_23__ __dummy_24__ =>
 (

(* Nop *)

{{ Return (mkst (comps) (tr ~~~ KRecv c (SysCreatePtyerRes __dummy_23__ __dummy_24__) :: tr) (system)
(slave)
(logincnt)
(loginsucceded)
(username)) }}
 ) 
    (* special case for errors *)
    | BadTag tag =>
      {{ Return (mkst comps (tr ~~~ KRecv c (BadTag tag) :: tr) system slave logincnt loginsucceded username) }}
    end
  );  sep unfoldr simplr.
Qed.

Fixpoint type_of_comp (c: tchan) (comps: list tchan): chan_type :=
  match comps with

| nil => System (* TODO: need default or proof *)
  | x :: rest =>
    if tchan_eq x c then
      projT1 x
    else
      type_of_comp c rest
  end.

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.

  intros kst.
  pose (comps := components kst);
  pose (tr := ktr kst);
  pose (system := system kst);
pose (slave := slave kst);
pose (logincnt := logincnt kst);
pose (loginsucceded := loginsucceded kst);
pose (username := username kst);
  refine (
    comp <- select comps
    (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ [KInvariant kst] * all_bound comps * [In system comps] * [In slave comps] * emp);
    let handler := (
      let p := projT1 comp in
      match p as p' return p = p' -> _ with
| System => fun _ => exchange_System comp _
| Slave => fun _ => exchange_Slave comp _
      end
    ) in
    s' <- handler _ (mkst comps (tr ~~~ KSelect comps comp :: tr) system 
slave 
logincnt 
loginsucceded 
username );
    {{ Return s' }}
  );
  sep unfoldr simplr.

Qed.

Definition kloop:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  intros; refine (
    Fix
      (fun s => kstate_inv s)
      (fun s s' => kstate_inv s')
      (fun self s =>
        s <- kbody s;
        s <- self s;
        {{ Return s }}
      )
    s
  );
  sep fail auto.
Qed.

Definition main:
  forall (_ : unit),
  STsep (traced nil)
        (fun s' => kstate_inv s').
Proof.
  intros; refine (
    s0 <- kinit tt;
    sN <- kloop s0;
    {{ Return sN }}
  );
  unfold kstate_inv;
  sep fail auto.
Qed.