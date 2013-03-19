Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import ReflexHVec.

Definition NB_MSG : nat := 3.

Definition PAY_DESC : vvdesc NB_MSG :=
  ( existT _ 0 tt (*A : echoed to user if n <> 0*)
   , ( existT _ 0 tt (*B : increments n by 1*)
   , ( existT _ 0 tt (*C : sets n = 0*)
    , tt))
  ).

Definition INIT_ENVD : vdesc := existT _ 0 tt.

Definition KST_DESC_SIZE := 1.

(*State is (username, authres)*)
Definition KST_DESC : vdesc' KST_DESC_SIZE := (num_d, tt).

Definition INIT : @init_prog NB_MSG PAY_DESC _ KST_DESC INIT_ENVD :=
  nil.

Definition HANDLERS : handlers (VVD := PAY_DESC) KST_DESC :=
  (fun m f st =>
    match tag m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag (VVD := PAY_DESC) _tm) -> _
    with
    | None => fun pl =>
       let envd := existT _ 0 tt in
       if num_eq (@shvec_ith _ _ _
                                (KST_DESC:svec desc KST_DESC_SIZE)
                                (kst _ st) None)
                    (num_of_nat 0)
       then existT _ envd (nil) (*Ignore.*)
       else existT _ envd (
                          Send _ _ _
                               (HEchan _ _)
                               (@MEmsg _ PAY_DESC envd None tt)
                               :: nil
                          )
    | Some None => fun _ =>
         let envd := existT _ 0 tt in
         let n := (@shvec_ith _ _ _
                                (KST_DESC:svec desc KST_DESC_SIZE)
                                (kst _ st) None) in
         existT _ envd (
                  STChange KST_DESC _ _
                    None (HEexpr _ _ _
                                 (MEbase _ _
                                    (BinOp envd _ _ _ Add
                                           (NLit _ n) (NLit _ (num_of_nat 1)))))
                    :: nil
                )
    | Some (Some None) => fun _ =>
         let envd := existT _ 0 tt in
         let n := (@shvec_ith _ _ _
                                (KST_DESC:svec desc KST_DESC_SIZE)
                                (kst _ st) None) in
         existT _ envd (
                  STChange KST_DESC _ _
                    None (HEexpr _ _ _
                                 (MEbase _ _ (NLit _ (num_of_nat 0))))
                                         (*(NLit _ ((num_of_nat (nat_of_num n) + 0)))))*)
                                    (*(BinOp envd _ _ _ Add
                                           (NLit _ n) (NLit _ (num_of_nat 0)))))*)
                    :: nil
                )
    | Some (Some (Some bad)) => fun _ =>
      match bad with end
    end (pay m)
  ).

Require Import Ynot.
Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.
Require Import List.

Theorem enable : forall st tr,
  Reach _ _ INIT HANDLERS st -> ktr _ st = inhabits tr ->
  Release NB_MSG PAY_DESC
           (@KORecv NB_MSG PAY_DESC None
                    (Some (@Build_opt_msg NB_MSG PAY_DESC
                                          (Some None) tt)))
           (@KOSend NB_MSG PAY_DESC None
                    (Some (@Build_opt_msg NB_MSG PAY_DESC
                                          None tt)))
           tr.
Proof.
  crush.
Qed.
