Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import ReflexHVec.
Require Import ReflexFin.
Require Import ReflexFrontend.

Open Scope string_scope.

Definition NB_MSG : nat := 2.

Definition PAYD : vvdesc NB_MSG :=
  mk_vvdesc
  [ ("Echo", []) (*Message to be echoed if the next message has not been received.*)
   ; ("Disable", []) (*Disabling message, sets n = 1.*)
  ].

(*State is (username, authres)*)
Definition KSTD : vdesc := mk_vdesc [num_d].
Definition st_n : fin (projT1 KSTD) := None.

Notation msg_echo := (None) (only parsing).
Notation msg_disable := (Some None) (only parsing).

Definition IENVD : vdesc := mk_vdesc [fd_d].

Inductive COMPT : Type := Stupid.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Stupid => mk_compd "Echo" "test/echo-00/test.py" [] (mk_vdesc [])
  end.

Definition IMSG : msg PAYD := @Build_msg _ PAYD None tt.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IMSG IENVD :=
  [fun s => Spawn _ _ COMPS _ _ IENVD Stupid tt None (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  (fun m cfd =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with
    | msg_echo => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
           fun st =>
           if num_eq (@shvec_ith _ _ (projT1 KSTD)
                                 (projT2 KSTD)
                                 (kst _ _ _ _ st) st_n)
                     (num_of_nat 0)
           then [ fun s => Send _ _ _ _ _ _ (CFd PAYD _ _ _) msg_echo tt ]
           else [] (*Ignore.*)
              )
    | msg_disable => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
           fun st =>
           [ fun _ => StUpd _ _ _ KSTD _ _ st_n numd_neq_fdd
                            (NLit _ _ _ _ (num_of_nat 1))]
      )
    | Some (Some bad) => fun _ =>
      match bad with end
    end (pay PAYD m)
  ).

Require Import Ynot.
Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.

Theorem disable : forall st tr,
  Reach _ _ COMPS _ _ _ INIT HANDLERS st -> ktr _ _ _ _ st = inhabits tr ->
  Disables PAYD
           (KORecv PAYD None
                    (Some (Build_opt_msg PAYD
                                          msg_disable tt)))
           (KOSend PAYD None
                    (Some (Build_opt_msg PAYD
                                          msg_echo tt)))
           tr.
Proof.
  crush.
Qed.