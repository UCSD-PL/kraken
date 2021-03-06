Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import ReflexHVec.
Require Import ReflexFin.
Require Import ReflexFrontend.

Open Scope string_scope.

Definition NB_MSG : nat := 3.

Definition PAYD : vvdesc NB_MSG :=
  mk_vvdesc
  [ ("User", [str_d]) (*User name payload.*)
   ; ("AuthSuc", [str_d]) (*Successful auth response from system payload.*)
   ; ("AuthFail", [str_d]) (*Failed auth response from system payload.*)
  ].

(*State is (username, authres)*)
Definition KSTD : vdesc := mk_vdesc [str_d; num_d].
Definition st_user : fin (projT1 KSTD) := None.
Definition st_authed : fin (projT1 KSTD) := Some None.

Notation msg_user := (None) (only parsing).
Notation msg_authed_suc := (Some None) (only parsing).
Notation msg_authed_fail := (Some (Some None)) (only parsing).

Definition IENVD : vdesc := mk_vdesc [fd_d].

Inductive COMPT : Type := Stupid.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Stupid => mk_compd "Echo" "test/echo-00/test.py" [] (mk_vdesc [])
  end.

Definition IMSG : msg PAYD := @Build_msg _ PAYD None (str_of_string "", tt).

Definition INIT : init_prog PAYD COMPT COMPS KSTD IMSG IENVD :=
  [fun s => Spawn _ _ COMPS _ _ IENVD Stupid tt None (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  (fun m cfd =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with
    | msg_user => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         let (u, _) := pl in fun st =>
           if num_eq (@shvec_ith _ _ (projT1 KSTD)
                                 (projT2 KSTD)
                                 (kst _ _ _ _ st) st_authed)
                                 (num_of_nat 0)
           then [] (*Ignore.*)
           else if str_eq (@shvec_ith _ _ (projT1 KSTD)
                                      (projT2 KSTD)
                                      (kst _ _ _ _ st) st_user)
                                      u
                then [ fun s => Send _ _ _ _ _ _
                                     (CFd PAYD _ _ _) None
                                     (SLit _ _ _ _ u, tt) ]
                else [] (*Ignore.*)
              )
    | msg_authed_suc => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
        let (u, _) := pl in fun st =>
        [ fun _ => StUpd _ _ _ KSTD _ _ st_user strd_neq_fdd
                         (SLit _ _ _ _ u)
        ; fun _ => StUpd _ _ _ KSTD _ _ st_authed numd_neq_fdd
                         (NLit _ _ _ _ (num_of_nat 1))
        ]
      )
    | msg_authed_fail => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
        let (u, _) := pl in fun st =>
        [ fun _ => StUpd _ _ _ KSTD _ _ st_user strd_neq_fdd 
                         (SLit _ _ _ _ u)
        ; fun _ => StUpd _ _ _ KSTD _ _ st_authed numd_neq_fdd
                         (NLit _ _ _ _ (num_of_nat 0))
        ]
      )
    | Some (Some (Some bad)) => fun _ =>
      match bad with end
    end (pay _ m)
  ).

Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.
Require Import List.
Require Import Ynot.

Theorem enables : forall st tr u,
  Reach _ _ COMPS _ _ _ INIT HANDLERS st -> ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD
          (KORecv PAYD None
                   (Some (Build_opt_msg PAYD
                                         (Some None) (Some u, tt))))
          (KOSend PAYD None
                   (Some (Build_opt_msg PAYD
                                         None (Some u, tt))))
          tr.
Proof.
  crush.
Qed.
