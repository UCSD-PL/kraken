Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import ReflexHVec.
Require Import ReflexFin.

Open Scope string_scope.

Definition NB_MSG : nat := 2.

Definition PAYD : vvdesc NB_MSG :=
  mk_vvdesc
  [ ("User", [str_d]) (*User name payload.*)
   ; ("Auth", [str_d; num_d]) (*Auth response from system payload.*)
  ].

(*State is (username, authres)*)
Definition KSTD : vdesc := mk_vdesc [str_d; num_d].
Definition st_user : fin (projT1 KSTD) := None.
Definition st_authed : fin (projT1 KSTD) := Some None.

Notation msg_user := (None) (only parsing).
Notation msg_authed := (Some None) (only parsing).

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
    | msg_user => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (
         let (u, _) := pl in fun st =>
           if num_eq (@shvec_ith _ _ (projT1 KSTD)
                                 (projT2 KSTD)
                                 (kst _ _ st) st_authed)
                                 (num_of_nat 0)
           then [] (*Ignore.*)
           else if str_eq (@shvec_ith _ _ (projT1 KSTD)
                                      (projT2 KSTD)
                                      (kst _ _ st) st_user)
                                      u
                then [ fun s => Send PAYD _ _ _ (CFd _ _) None (SLit _ _ u, tt) ]
                else [] (*Ignore.*)
              )
    | msg_authed => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (
        let (u, pl') := pl in
        let (res, _) := pl' in fun st =>
        [ fun _ => StUpd _ _ KSTD _ st_user strd_neq_fdd  (SLit _ _ u)
        ; fun _ => StUpd _ _ KSTD _ st_authed numd_neq_fdd (NLit _ _ res)
        ]
      )
    | Some (Some bad) => fun _ =>
      match bad with end
    end (pay _ m)
  ).

Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.
Require Import Ynot.

Theorem release : forall st tr u,
  Reach _ _ COMPS _ _ INIT HANDLERS st -> ktr _ _ st = inhabits tr ->
  Release PAYD
          (KORecv PAYD None
                   (Some (Build_opt_msg PAYD
                                         (Some None) (Some u, (None, tt)))))
          (KOSend PAYD None
                   (Some (Build_opt_msg PAYD
                                         None (Some u, tt))))
          tr.
Proof.
  crush.
Qed.
