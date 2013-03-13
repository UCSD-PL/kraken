Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import ReflexHVec.

Definition NB_MSG : nat := 3.

Definition PAY_DESC : vvdesc NB_MSG :=
  ( existT _ 1 (str_d, tt) (*User name payload.*)
   , ( existT _ 1 (str_d, tt) (*Successful auth response from system payload.*)
   , ( existT _ 1 (str_d, tt) (*Failed auth response from system payload.*)
    , tt))
  ).

Definition INIT_ENVD : vdesc := existT _ 0 tt.

Definition KST_DESC_SIZE := 2.

(*State is (username, authres)*)
Definition KST_DESC : vdesc' KST_DESC_SIZE := (str_d, (num_d, tt)).

Definition INIT : @init_prog NB_MSG PAY_DESC _ KST_DESC INIT_ENVD :=
  nil.

Definition HANDLERS : handlers (VVD := PAY_DESC) KST_DESC :=
  (fun m f st =>
    match tag m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag (VVD := PAY_DESC) _tm) -> _
    with
    | None => fun pl =>
       let (u, _) := pl in
       let envd := existT _ 0 tt in
       if num_eq (@shvec_ith _ _ _
                                (KST_DESC:svec desc KST_DESC_SIZE)
                                (kst _ st) (Some None))
                    (num_of_nat 0)
       then existT _ envd (nil) (*Ignore.*)
       else if str_eq (@shvec_ith _ _ _
                                (KST_DESC:svec desc KST_DESC_SIZE)
                                (kst _ st) None)
                    u
            then existT _ envd (
                          let (u, _) := pl in
                          Send _ _ _
                               (HEchan _ _)
                               (@MEmsg _ PAY_DESC envd None (SLit _ u, tt))
                               :: nil
                          )
            else existT _ envd (nil) (*Ignore.*)
    | Some None => fun pl =>
       let envd := existT _ 0 tt in
       existT _ envd (
        let (u, _) := pl in
        STChange KST_DESC _ _
          None (HEexpr _ _ _ (MEbase _ _ (SLit _ u)))
        :: STChange KST_DESC _ _
             (Some None) (HEexpr _ _ _ (MEbase _ _ (NLit _ (num_of_nat 1))))
        :: nil
      )
    | Some (Some None) => fun pl =>
       let envd := existT _ 0 tt in
       existT _ envd (
        let (u, _) := pl in
        STChange KST_DESC _ _
          None (HEexpr _ _ _ (MEbase _ _ (SLit _ u)))
        :: STChange KST_DESC _ _
             (Some None) (HEexpr _ _ _ (MEbase _ _ (NLit _ (num_of_nat 0 ))))
        :: nil
      )
    | Some (Some (Some bad)) => fun _ =>
      match bad with end
    end (pay m)
  ).

Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.
Require Import List.
Require Import Ynot.

Theorem release : forall st tr u,
  Reach _ _ INIT HANDLERS st -> ktr _ st = inhabits tr ->
  Release NB_MSG PAY_DESC
          (@KORecv NB_MSG PAY_DESC None
                   (Some (@Build_opt_msg NB_MSG PAY_DESC
                                         (Some None) (Some u, tt))))
          (@KOSend NB_MSG PAY_DESC None
                   (Some (@Build_opt_msg NB_MSG PAY_DESC
                                         None (Some u, tt))))
          tr.
Proof.
  crush.
Qed.
