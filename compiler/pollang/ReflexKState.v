Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import ReflexHVec.

Definition NB_MSG : nat := 2.

Definition PAY_DESC : vvdesc NB_MSG :=
  ( existT _ 1 (str_d, tt) (*User name payload.*)
   , ( existT _ 2 (str_d, (num_d, tt)) (*Auth response from system payload.*)
    , tt)
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
       let envd := existT _ 0 tt in
       match num_eq (@shvec_ith _ _ _
                                (KST_DESC:svec desc KST_DESC_SIZE)
                                (kst _ st) (Some None))
                    (num_of_nat 0)
       with
       | left _ => existT _ envd (nil) (*Ignore.*)
       | right _ => existT _ envd (
                             let (u, _) := pl in
                             Send _ _ _
                                  (HEchan _ _)
                                  (@MEmsg _ PAY_DESC envd None (SLit _ u, tt))
                             :: nil
                           )
       end
    | Some None => fun pl =>
       let envd := existT _ 0 tt in
       existT _ envd (
        let (u, pl') := pl in
        let (res, _) := pl' in
        STChange KST_DESC _ _
          None (HEexpr _ _ _ (MEbase _ _ (SLit _ u)))
        :: STChange KST_DESC _ _
             (Some None) (HEexpr _ _ _ (MEbase _ _ (NLit _ res)))
        :: nil
      )
    | Some (Some bad) => fun _ =>
      match bad with end
    end (pay m)
  ).