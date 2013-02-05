Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import Regex.
Require Import Ynot.

Definition NB_MSG : nat := 1.

Definition PDV : payload_desc_vec NB_MSG :=
  ( existT _ 1 (str_d, tt)
  , tt
  ).

Definition HANDLERS : @handler NB_MSG PDV :=
  (fun m =>
    match tag m as _tm return
      @sdenote _ SDenoted_payload_desc (@lkup_tag NB_MSG PDV _tm) -> _
    with
    | None => fun pl =>
      let (s, _) := pl in
         Send m (CurChan m) (MsgExpr m None (SLit m s, tt))
      :: nil
    | Some bad => fun _ =>
      match bad with end
    end (pay m)
  )
.

Definition send_star NB_MSG PDV :=
  RE_Star (RE_Alt (RE_Atom (@KOSend NB_MSG PDV None None))
                  (RE_Atom (@KOExec NB_MSG PDV None None None))).

Ltac unpack :=
  match goal with
  | [ H: [_]%inhabited = [_]%inhabited |- _ ] =>
    apply pack_injective in H;
    rewrite -> H in * || rewrite <- H in *
  end.

Theorem always_send : forall st tr,
  Reach HANDLERS st -> inhabits tr = ktr st ->
  RMatch (send_star NB_MSG PDV) tr.
