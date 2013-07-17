Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
Require Import ReflexHVec.
Require Import ReflexIO.
Require Import ReflexVec.

Open Scope string_scope.

(*
 This SSH monitor works as follows :
 1) the SSH monitor(MON) creates 3 different comps : SYS, SLV, PTY
 2) MON waits till SLV sends LoginReq

 == Login Request
 1) SLV asks MON to login via LoginReq,
 1-1) if login_cnt =n 3 then send Login_Res(0) back to SLV
 1-2) otherwise, login_cnt = login_cnt + 1, then send SysLogReq()
 to SYS

 2) SYS replies to MON with SysLogRes()
 if the response is 1 then set login_succeded = 1; and
 login_account = $account and MON delivers it to SLV with LogRes

 == PubKey Request
 1) SLV asks MON for the public key via PubKeyReq
 MON delivers it to SYS via SysPubKeyReq

 2) SYS replies to MON with SysPubKeyRes
 MON delivers it to SLV

 == KeySign Request(str)/IOCTL(fdesc)
 works in the same as as PubKeyRequest

 == CreatePtyer
 1) SLV asks MON for a created PTYER
 1-1) if login_succeeded =n 0 then ignore this request completely
 and don't send anything back

 2) MON creates a PTY by sending SysCreatePtyReq()
 3) SYS sends back with SysCreatPtyRes(fdesc, fdesc)
 (SYS applies ioctl() to the slave fd & it creates a ptyer inside it
 (Question: there are two options : a. create ptyer inside SYS
 b. spawns a ptyer as a component from MON. Which one is better?? )

 4) MON replies back to SLV with the two file descriptors
*)

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 18.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [
    (* slave <- monitor *)
    ("LoginReq",   [str_d]);
    ("LoginResT",   []);
    ("LoginResF",   []);

    ("PubkeyReq",   []);
    ("PubkeyRes",   [str_d]);

    ("KeysignReq",   [str_d]);
    ("KeysignRes",   [str_d]);

    ("CreatePtyerReq",   []);
    ("CreatePtyerRes",   [fd_d; fd_d]);

    (* monitor <-> system *)
    ("SLoginReq",   [str_d]);
    ("SLoginResT",   [str_d]);
    ("SLoginResF",   []);

    ("SPubkeyReq",   []);
    ("SPubkeyRes",   [str_d]);

    ("SKeysignReq",   [str_d]);
    ("SKeysignRes",   [str_d]);

    ("SCreatePtyerReq",   [str_d]);
    ("SCreatePtyerRes",   [fd_d; fd_d])
  ].

Inductive COMPT' : Type := System | Slave.

Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | System => mk_compd
                "System" "/home/don/kraken/kraken/ssh-proto/kmsg-ssh/sshd_sys" []
                (mk_vdesc [str_d])
  | Slave  => mk_compd
                "Slave"  "/home/don/kraken/kraken/ssh-proto/kmsg-ssh/ssh"      []
                (mk_vdesc [])
  end.

Notation LoginReq        := 0%fin (only parsing).
Notation LoginResT       := 1%fin (only parsing).
Notation LoginResF       := 2%fin (only parsing).
Notation PubkeyReq       := 3%fin (only parsing).
Notation PubkeyRes       := 4%fin (only parsing).
Notation KeysignReq      := 5%fin (only parsing).
Notation KeysignRes      := 6%fin (only parsing).
Notation CreatePtyerReq  := 7%fin (only parsing).
Notation CreatePtyerRes  := 8%fin (only parsing).
Notation SLoginReq       := 9%fin (only parsing).
Notation SLoginResT      := 10%fin (only parsing).
Notation SLoginResF      := 11%fin (only parsing).
Notation SPubkeyReq      := 12%fin (only parsing).
Notation SPubkeyRes      := 13%fin (only parsing).
Notation SKeysignReq     := 14%fin (only parsing).
Notation SKeysignRes     := 15%fin (only parsing).
Notation SCreatePtyerReq := 16%fin (only parsing).
Notation SCreatePtyerRes := 17%fin (only parsing).

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ System; Comp _ Slave ].

Notation v_env_system := (None) (only parsing).
Notation v_env_slave  := (Some None) (only parsing).

Definition KSTD : vcdesc COMPT := mk_vcdesc
  [ Comp _ System
  ; Comp _ Slave
  ; Desc _ num_d (* authenticated *)
  ; Desc _ str_d (* authenticated username *)
  ].

Notation v_st_system        := (None) (only parsing).
Notation v_st_slave         := (Some None) (only parsing).
Notation v_st_authenticated := (Some (Some None)) (only parsing).
Notation v_st_auth_user     := (Some (Some (Some None))) (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec <: SpecInterface.

Include SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
   seq (spawn _ IENVD System (str_of_string "System", tt) v_env_system (Logic.eq_refl _))
  (seq (stupd _ IENVD v_st_system (i_envvar IENVD v_env_system))
  (seq (spawn _ IENVD Slave  tt                           v_env_slave  (Logic.eq_refl _))
       (stupd _ IENVD v_st_slave (i_envvar IENVD v_env_slave)))).

Definition system_pat := (Some (str_of_string "System"), tt).

Definition exists_comp := exists_comp COMPT COMPTDEC COMPS.

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match ct as _ct, t as _t return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
     | Slave, LoginReq =>
       [[ mk_vcdesc [] :
          send (stvar v_st_system) SLoginReq (mvar LoginReq 0%fin, tt)
       ]]
     | System, SLoginResT =>
       [[ mk_vcdesc [] :
           seq (stupd _ _ v_st_auth_user     (mvar SLoginResT 0%fin))
          (seq (stupd _ _ v_st_authenticated (nlit (num_of_nat 1)))
               (send (stvar v_st_slave) LoginResT tt))
       ]]
     | System, SLoginResF =>
       [[ mk_vcdesc [] :
          send (stvar v_st_slave) LoginResF tt
       ]]
     | Slave, PubkeyReq =>
       [[ mk_vcdesc [] :
          send (stvar v_st_system) SPubkeyReq tt
       ]]
     | System, SPubkeyRes =>
       [[ mk_vcdesc [] :
          send (stvar v_st_slave) PubkeyRes (mvar SPubkeyRes 0%fin, tt)
       ]]
     | Slave, KeysignReq =>
       [[ mk_vcdesc [] :
          send (stvar v_st_system) SKeysignReq (mvar KeysignReq 0%fin, tt)
       ]]
     | System, SKeysignRes =>
       [[ mk_vcdesc [] :
          send (stvar v_st_slave) KeysignRes (mvar SKeysignRes 0%fin, tt)
       ]]
     | Slave, CreatePtyerReq =>
       [[ mk_vcdesc [] :
          ite (eq (stvar v_st_authenticated) (nlit (num_of_nat 0)))
              (
                nop
              )
              (
                send (stvar v_st_system) SCreatePtyerReq (stvar v_st_auth_user, tt)
              )
       ]]
     | System, SCreatePtyerRes =>
       [[ mk_vcdesc [] :
          send (stvar v_st_slave) CreatePtyerRes
            (mvar SCreatePtyerRes 0%fin, (mvar SCreatePtyerRes 1%fin, tt))
       ]]
     | _, _ => [[ mk_vcdesc [] : nop ]]
    end.

Require Import PolLang.
Require Import ActionMatch.

Local Opaque str_of_string.

Definition System_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS System (Some (str_of_string "System"), tt).

Theorem enable : forall st tr u,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
          (KORecv PAYD COMPT COMPS (Some System_pat)
                   (Some (Build_opt_msg PAYD
                                         SLoginResT (Some u, tt))))
          (KOSend PAYD COMPT COMPS None
                   (Some (Build_opt_msg PAYD
                                         SCreatePtyerReq (Some u, tt))))
          tr.
Proof.
  crush.
(*Ltac match_releases :=
  match goal with
  | [ |- Enables _ _ _ _ _ _ nil ]
      => constructor
  (* Induction hypothesis.*)
  | [ H : Reflex.ktr _ _ _ _ ?s = inhabits ?tr,
      IH : forall tr', Reflex.ktr _ _ _ _ ?s = inhabits tr' ->
                       Enables _ _ _ _ ?past ?future tr'
                       |- Enables _ _ _ _ ?past ?future ?tr ]
      => auto
  (*Branch on whether the head of the trace matches.*)
  | [ |- Enables ?pdv ?compt ?comps ?comptdec _ ?future (?act::_) ]
      => (*let s := match goal with
                  | [ _ : ktr _ _ _ _ ?s = inhabits _ |- _ ]
                      => s
                  | [ s : init_state _ _ _ _ _ |- _ ]
                      => s
                  end in*)
         let H := fresh "H" in
         pose proof (decide_act pdv compt comps comptdec future act) as H;
         destruct H;
         [ first [ contradiction | destruct_action_matches; contradiction |
           (apply E_future; [ match_releases | (*try exists_past*) ]) ]
         | first [ contradiction | destruct_action_matches; contradiction |
           (apply E_not_future; [ match_releases | assumption ]) ] ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  end.
reach_induction; try abstract match_releases.

match_releases.
destruct_action_matches.
Ltac releaser_match :=
  simpl;
  repeat match goal with
         | [ |- exists past : Reflex.KAction _ _ _, (?act = _ \/ ?disj_R ) /\ ?conj_R ]
           => solve [exists act; split; [left; try subst; auto | compute; try subst; auto] ] ||
              apply cut_exists
         end.
releaser_match.
clear_useless_hyps.
generalize dependent tr.
induction H.
  abstract (intros; inversion H; subst s0; subst s; simpl in *;
  uninhabit; impossible).

  inversion H0. subst s'0. subst s'.
  Ltac leaf_solve :=
  simpl; try destruct_ite; simpl; intros;
  try abstract (
  uninhabit;
  match goal with
  | [ _ : Reflex.InitialState _ _ _ _ _ _ _ _ _ |- _ ]
    => try subst; simpl in *;
       try solve [ impossible
                 | releaser_match ]
  | [ _ : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ _ |- _ ]
    => try subst; simpl in *;
       try solve [ impossible
                 | use_IH_releases
                 | releaser_match
                 (*| exists_past*)]
        (*destruct_eq might have created contradictions
           with previous calls of destruct_eq*)
  | [ _ : Reflex.BogusExchange _ _ _ _ _ _ _ _ |- _ ]
    => try subst; simpl in *; use_IH_releases
  | _ => idtac
  end).

Ltac destruct_solve tag pay :=
  match type of tag with
  | False => contradiction
  | _ => let tag' := fresh "tag" in
          destruct tag as [tag' | ];
          [ | try (destruct_pay pay; leaf_solve) ]
          (*destruct_solve tag' pay*)
  | _ => idtac
  end.
  destruct_comp; destruct m as [tag pay].
  destruct_solve tag pay.
  destruct_solve tag0 pay.
  destruct_solve tag pay.
  destruct_solve tag0 pay.
Focus 2.
simpl in *. unfold hdlrs in H1. destruct_comp. simpl in H1.
uninhabit. try subst. idtac. use_IH_releases.
  destruct_msg; destruct_comp.
destruct s.
destruct kst.
destruct s1.
destruct p.
destruct p.

intros.
  generalize dependent tr.
 induction H.
   unpack. abstract match_releases.

   inversion H0. subst s'0. subst s'. 

Ltac leaf_solve :=
  simpl; try destruct_ite; simpl; intros; try abstract (uninhabit; match_releases).

Ltac destruct_solve tag pay :=
  match type of tag with
  | False => contradiction
  | _ => let tag' := fresh "tag" in
          destruct tag as [tag' | ];
          [ | try (destruct_pay pay; leaf_solve) ];
          try (destruct_solve tag' pay)
  end.

destruct_comp; destruct m as [tag pay]. destruct_solve tag pay. destruct_solve tag pay.

Ltac releaser_match :=
  simpl;
  repeat match goal with
         | [ |- exists past : Reflex.KAction _ _ _, (?act = _ \/ ?disj_R ) /\ ?conj_R ]
           => solve [exists act; split; [left; try subst; auto | compute; try subst; auto] ] ||
              apply cut_exists
         end.

Ltac exists_past :=
  destruct_action_matches;
  (*There may be conditions on s' (the intermediate state). We want
    to use these conditions to derive conditions on s.*)
  (*subst_states;*)
  (*Try to match stuff at head of trace.*)
  releaser_match;
  (*This may not clear the old induction hypothesis. Does it matter?*)
  clear_useless_hyps(*;
  (*Should this take s as an argument?*)
  reach_induction;
  try abstract
  (match goal with
  | [ _ : Reflex.InitialState _ _ _ _ _ _ _ _ _ |- _ ]
    => try subst; simpl in *;
       try solve [ impossible
                 | releaser_match ]
  | [ _ : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ _ |- _ ]
    => try subst; simpl in *;
       try solve [ impossible
                 | use_IH_releases
                 | releaser_match
                 (*| exists_past*)]
        (*destruct_eq might have created contradictions
           with previous calls of destruct_eq*)
  | [ _ : Reflex.BogusExchange _ _ _ _ _ _ _ _ |- _ ]
    => try subst; simpl in *; use_IH_releases
  | _ => idtac
  end)*).
simpl. intros; uninhabit.
match_releases.
idtac.
destruct_action_matches.
releaser_match.
clear_useless_hyps.
exists_past.
generalize dependent tr.
Ltac unpack :=
  match goal with
  | [ H : Reflex.InitialState _ _ _ _ _ _ _ _ ?s |- _ ]
    => inversion H;
       match goal with
       | [ _ : ?s' = init_state_run_cmd _ _ _ _ _ _ _ _ _ |- _ ]
         => subst s'; subst s
       end
  | [ H : Reflex.ValidExchange _ _ _ _ _ _ _ _ _ _ ?s |- _ ]
    => destruct_msg; destruct_comp; inversion H;
       match goal with
       | [ _ : ?s' = mk_inter_ve_st _ _ _ _ _ _ _ _ |- _ ]
         => subst s'; subst s
       end
  | [ H : Reflex.BogusExchange _ _ _ _ _ _ _ ?s |- _ ]
    => inversion H; subst s
  end; simpl; try destruct_ite_pol; simpl in *; intros; uninhabit.
induction H; try unpack.

  impossible.

  destruct_msg; destruct_comp.
    inversion H0. subst s'0. subst s'. simpl. try destruct_ite_pol. intros. uninhabit.*)
Qed.

End Spec.

Module Main := MkMain(Spec).
Import Main.
(*
Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.
Require Import Ynot.

Import Spec.

Local Opaque str_of_string.

Ltac destruct_fin f :=
  match type of f with
  | False => destruct f
  | _ => let f' := fresh "f" in
         destruct f as [ f' | ]; [destruct_fin f' | ]
  end.

Ltac destruct_pay pay :=
  vm_compute in pay;
  match type of pay with
  | unit => idtac
  | _ =>
    let x := fresh "x" in
    let r := fresh "r" in
    destruct pay as [x r]; simpl in x; destruct_pay r
  end.

Ltac destruct_msg :=
  match goal with [ m : msg _ |- _ ] =>
    let tag := fresh "tag" in
    let pay := fresh "pay" in
    destruct m as [tag pay]; destruct_fin tag; destruct_pay pay
  end.

(*Destructs num, str, or fd equalities in the context.*)
Ltac destruct_eq H :=
  repeat match type of H with
         | context[if ?x then _ else _ ]
           => destruct x
         end.

Ltac destruct_input input :=
  unfold cmd_input in *;
  simpl in *; (*compute in input;*)
  match type of input with
  | unit => idtac
  | _ => let x := fresh "x" in
         let input' := fresh "input'" in
         destruct input as [x input']; destruct_input input'
  end.

Ltac unpack_inhabited Htr :=
  match type of Htr with
  | _ = inhabits ?tr
     => simpl in Htr; apply pack_injective in Htr; subst tr
  end.

Ltac unpack :=
  match goal with
  | [ Htr : ktr _ _ _ _ ?s = inhabits ?tr |- _ ] =>
    match goal with
    (*Valid exchange.*)
    | [ c : comp _ _, _ : ?s' = _,
        input : kstate_run_prog_return_type _ _ _ _ _ _ _ _ ?s' _ |- _ ] =>
      subst s'; destruct c; destruct_eq Htr; destruct_input input
    (*Initialization.*)
    | [ s : init_state _ _ _ _ _,
        input : init_state_run_prog_return_type _ _ _ _ _ _ _ _ |- _ ] =>
      match goal with
      | [ H : s = _ |- _ ] =>
        rewrite H in Htr; destruct_input input
      end
    (*Bogus msg*)
    | [ c : comp _ _ |- _ ] =>
      subst s; destruct c
    end(*; unpack_inhabited Htr*)
  end.

Ltac destruct_unpack :=
  match goal with
  | [ m : msg _ |- _ ]
      => destruct_msg; unpack
  | _
      => unpack
  end.

Ltac reach_induction :=
  intros;
  match goal with
  | [ _ : ktr _ _ _ _ _ = inhabits ?tr, H : Reach _ _ _ _ _ _ _ _ _ |- _ ]
      => generalize dependent tr; induction H;
         (*Do not put simpl anywhere in here. It breaks destruct_unpack.*)
         intros; destruct_unpack
  end.

Theorem Enables_app : forall A B tr tr',
  (forall elt, List.In elt tr' -> ~ PolLang.AMatch PAYD COMPT COMPS COMPTDEC B elt) ->
  Enables PAYD COMPT COMPS COMPTDEC A B tr ->
  Enables PAYD COMPT COMPS COMPTDEC A B (tr' ++ tr)%list.
Proof.
  intros. induction tr'.
  now simpl.
  apply E_not_future. apply IHtr'. intros. apply H. now right.
  apply H. now left.
Qed.

Theorem auth_priv : forall st tr u,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
          (KORecv PAYD COMPT COMPS None
                  (Some (Build_opt_msg PAYD
                                       SLoginResT (Some u, tt))))
          (KOSend PAYD COMPT COMPS None
                  (Some (Build_opt_msg PAYD
                                       SCreatePtyerReq (Some u, tt))))
          tr.
Proof.
  admit. (*reach_induction.*)
Qed.
*)