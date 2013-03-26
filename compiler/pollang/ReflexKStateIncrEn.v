Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import ReflexHVec.
Require Import ReflexFin.

Open Scope string_scope.

Definition NB_MSG : nat := 3.

Definition PAYD : vvdesc NB_MSG :=
  mk_vvdesc
  [ ("Echo", []) (*A : echoed to user if n <> 0*)
   ; ("Enable", []) (*B : increments n by 1*)
   ; ("Nothing", []) (*C : sets n = 0*)
  ].

(*State is (username, authres)*)
Definition KSTD : vdesc := mk_vdesc [num_d].
Definition st_n : fin (projT1 KSTD) := None.

Notation msg_echo := (None) (only parsing).
Notation msg_enable := (Some None) (only parsing).
Notation msg_nothing := (Some (Some None)) (only parsing).

Definition IENVD : vdesc := mk_vdesc [].

Inductive COMPT : Type := Stupid.

Definition COMPS (t : COMPT) : comp :=
  match t with
  | Stupid => mk_comp "Echo" "test/echo-00/test.py" []
  end.

Definition INIT : init_prog PAYD COMPT KSTD IENVD := [].

Definition HANDLERS : handlers PAYD COMPT KSTD :=
  (fun m cfd =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with
    | msg_echo => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (
           fun st =>
           if num_eq (@shvec_ith _ _ (projT1 KSTD)
                                 (projT2 KSTD)
                                 (kst _ _ st) st_n)
                     (num_of_nat 0)
           then [] (*Ignore.*)
           else [ fun s => Send PAYD _ _ _ (CFd _ _) msg_echo tt ]
              )
    | msg_enable => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (
           fun st =>
           let n := (@shvec_ith _ _ (projT1 KSTD)
                                 (projT2 KSTD)
                                 (kst _ _ st) st_n) in
           [ fun _ => StUpd _ _ KSTD _ st_n numd_neq_fdd
                            (BinOp KSTD _ _ _ _ Add
                                   (NLit _ _ n) (NLit _ _ (num_of_nat 1)))]
      )
    | msg_nothing => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (
           fun st =>
           [ fun _ => StUpd _ _ KSTD _ st_n numd_neq_fdd (NLit _ _ (num_of_nat 0))]
      )
    | Some (Some (Some bad)) => fun _ =>
      match bad with end
    end (pay PAYD m)
  ).

Require Import Ynot.
Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.
Require Import List.

Theorem enable : forall st tr,
  Reach _ _ COMPS _ _ INIT HANDLERS st -> ktr _ _ st = inhabits tr ->
  Release PAYD
           (KORecv PAYD None
                    (Some (Build_opt_msg PAYD
                                          (Some None) tt)))
           (KOSend PAYD None
                    (Some (Build_opt_msg PAYD
                                          None tt)))
           tr.
Proof.
  crush.
Qed.
