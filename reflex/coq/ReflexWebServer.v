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

(*There are four different types of components: AC (Access Control), D (Disk), L (Listener), C (Client).
1) Initially, the kernel spawns one AC, one D, and one L.
2) The kernel waits until it receives a LoginReq from L.

== Login Request
1) L asks the kernel to login user u with password p at address a via LoginReq(u,p,a). The kernel sends ACLoginReq(u,p,a) to AC.

== Login Response
1) AC replies to kernel with ACLoginResT(u,a) or ACLoginResF(u,a).
2-1) ACLoginResT(u,a): if there is no client component with user u and address a, the kernel spawns a new Client component C(u,a) with user u and address a, and the kernel sends LoginResT(u,a) to L.
2-2) ACLoginResF(u,a): the kernel sends LoginResF(u,a) to L.

== File Access Request
1) C(u,a) asks the kernel for access to resource r via FileReq(r).
2) The kernel sends ACFileReq(u,a,r) to AC.

== File Access Response
1) AC responds with ACFileResT(u,a,r) or ACFileResF(u,a,r).
2-1) ACFileResT(u,a,r): the kernel sends DFileReq(u,a,r) to D, D replies with DFileRes(u,a,r,f), the kernel sends file descriptor f to C(u,a) via FileRes(r,f).
2-2) ACFileResF(u,a,r): the kernel sends FileResF(r) to C(u,a).

== Security Policies
1) AuthCorrect: forall u a, `Recv AC ACLoginResT(u,a)' Enables `Spawn C(u,a)'
2) AccessCorrect: forall u a r, `Recv AC ACFileResT(u,a,r)' Enables `Send D DFileReq(u,a,r)'

This is a very simple first design. Since we don't have maps in the kernel, we have to send unnecessary information to AC and D. In particular, we have to send the address of a client to AC, even though that information is never used by AC, and we have to send the user and address of a client to D, even though that information is never used by D. Basically, AC and D do some bookkeeping for the kernel. Eventually, we will add maps to the kernel.
*)

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 15.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [
    (*==Login Request*)
    (*LoginReq(u,p,a)*)
    ("LoginReq", [str_d; str_d; str_d]);
    (*ACLoginReq(u,p,a)*)
    ("ACLoginReq", [str_d; str_d; str_d]);
    (*ClientExists(u,a)*)
    ("ClientExists", [str_d; str_d]);

    (*==Login Response*)
    (*ACLoginResT(u,a)*)
    ("ACLoginResT", [str_d; str_d]);
    (*ACLoginResF(u,a)*)
    ("ACLoginResF", [str_d; str_d]);
    (*LoginResT(u,a)*)
    ("LoginResT", [str_d; str_d]);
    (*LoginResF(u,a)*)
    ("LoginResF", [str_d; str_d]);

    (*==File Access Request*)
    (*FileReq(r)*)
    ("FileReq", [str_d]);
    (*ACFileReq(u,a,r)*)
    ("ACFileReq", [str_d; str_d; str_d]);

    (*==File Access Response*)
    (*ACFileResT(u,a,r)*)
    ("ACFileResT", [str_d; str_d; str_d]);
    (*ACFileResF(u,a,r)*)
    ("ACFileResF", [str_d; str_d; str_d]);
    (*DFileReq(u,a,r)*)
    ("DFileReq", [str_d; str_d; str_d]);
    (*DFileRes(u,a,r,f)*)
    ("DFileRes", [str_d; str_d; str_d; fd_d]);
    (*FileRes(r,f)*)
    ("FileRes", [str_d; fd_d]);
    (*FileResF(r)*)
    ("FileResF", [str_d])
  ].

Inductive COMPT' : Type := AccessControl | Disk | Listener | Client.

Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition comp_dir := "".

Definition COMPS (t : COMPT) : compd :=
  match t with
  | AccessControl => mk_compd
                     "AccessControl" (comp_dir ++ "/access-control.py") []
                     (mk_vdesc [])
  | Disk  => mk_compd
             "Disk" (comp_dir ++ "/disk.py") []
             (mk_vdesc [])
  | Listener  => mk_compd
                 "Listener" (comp_dir ++ "/listener.py") []
                 (mk_vdesc [])
  | Client  => mk_compd
               "Client" (comp_dir ++ "/client.py") []
               (mk_vdesc [str_d; str_d])
  end.

Notation LoginReq := 0%fin (only parsing).
Notation ACLoginReq := 1%fin (only parsing).
Notation ClientExists := 2%fin (only parsing).
Notation ACLoginResT := 3%fin (only parsing).
Notation ACLoginResF := 4%fin (only parsing).
Notation LoginResT := 5%fin (only parsing).
Notation LoginResF := 6%fin (only parsing).
Notation FileReq := 7%fin (only parsing).
Notation ACFileReq := 8%fin (only parsing).
Notation ACFileResT := 9%fin (only parsing).
Notation ACFileResF := 10%fin (only parsing).
Notation DFileReq := 11%fin (only parsing).
Notation DFileRes := 12%fin (only parsing).
Notation FileRes := 13%fin (only parsing).
Notation FileResF := 14%fin (only parsing).

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ AccessControl; Comp _ Disk; Comp _ Listener ].

Notation v_env_ac := 0%fin (only parsing).
Notation v_env_d  := 1%fin (only parsing).
Notation v_env_l  := 2%fin (only parsing).

Definition KSTD : vcdesc COMPT := mk_vcdesc
  [ Comp _ AccessControl
  ; Comp _ Disk
  ; Comp _ Listener
  ].

Notation v_st_ac := 0%fin (only parsing).
Notation v_st_d  := 1%fin (only parsing).
Notation v_st_l  := 2%fin (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec <: SpecInterface.

Include SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
   seq (spawn _ IENVD AccessControl tt v_env_ac (Logic.eq_refl _))
  (seq (stupd _ IENVD v_st_ac (i_envvar IENVD v_env_ac))
  (seq (spawn _ IENVD Disk tt v_env_d (Logic.eq_refl _))
  (seq (stupd _ IENVD v_st_d (i_envvar IENVD v_env_d))
  (seq (spawn _ IENVD Listener tt v_env_l (Logic.eq_refl _))
       (stupd _ IENVD v_st_l (i_envvar IENVD v_env_l)))))).

Definition cur_client_u {t envd} :=
  cconf (envd:=envd) (t:=t) Client Client 0%fin (CComp PAYD COMPT COMPS KSTD Client t envd).

Definition cur_client_a {t envd} :=
  cconf (envd:=envd) (t:=t) Client Client 1%fin (CComp PAYD COMPT COMPS KSTD Client t envd).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match ct as _ct, t as _t return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
     | Listener, LoginReq =>
       [[ mk_vcdesc [] :
         send (stvar v_st_ac) ACLoginReq
             (mvar LoginReq 0%fin,
               (mvar LoginReq 1%fin, (mvar LoginReq 2%fin, tt)))
       ]]
     | AccessControl, ACLoginResT =>
       let envd := mk_vcdesc [Comp _ Client] in
       [[ envd :
          complkup (envd:=envd) (mk_comp_pat _ envd Client (None, (Some (mvar ACLoginResT 1%fin), tt)))
           nop
           (seq (spawn _ envd Client (mvar ACLoginResT 0%fin, (mvar ACLoginResT 1%fin, tt))
                 0%fin (Logic.eq_refl _))
                (send (stvar v_st_l) LoginResT
                  (mvar ACLoginResT 0%fin, (mvar ACLoginResT 1%fin, tt))))
       ]]
    | AccessControl, ACLoginResF =>
      [[ mk_vcdesc [] :
        send (stvar v_st_l) LoginResF (mvar ACLoginResF 0%fin, (mvar ACLoginResF 1%fin, tt))
      ]]
    | Client, FileReq =>
      [[ mk_vcdesc [] :
        send (stvar v_st_ac) ACFileReq (cur_client_u, (cur_client_a, (mvar FileReq 0%fin, tt)))
      ]]
    | AccessControl, ACFileResT =>
      [[ mk_vcdesc [] :
        send (stvar v_st_d) DFileReq
          (mvar ACFileResT 0%fin,
            (mvar ACFileResT 1%fin, (mvar ACFileResT 0%fin, tt)))
      ]]
    | AccessControl, ACFileResF =>
      let envd := mk_vcdesc [] in
      [[ envd :
        complkup (envd:=envd) (mk_comp_pat _ envd Client (None, (Some (mvar ACFileResF 1%fin), tt)))
          (send (envvar (mk_vcdesc [Comp _ Client]) 0%fin) FileResF (mvar ACFileResF 2%fin, tt))
          nop
      ]]
    | Disk, DFileRes =>
      let envd := mk_vcdesc [] in
      [[ envd :
        complkup (envd:=envd) (mk_comp_pat _ envd Client (None, (Some (mvar DFileRes 1%fin), tt)))
          (send (envvar (mk_vcdesc [Comp _ Client]) 0%fin) FileRes
            (mvar DFileRes 2%fin, (mvar DFileRes 3%fin, tt)))
          nop
      ]]
    | _, _ => [[ mk_vcdesc [] : nop ]]
    end.

Require Import PolLang.
Require Import ActionMatch.

Local Opaque str_of_string.

Definition AC_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS AccessControl tt.

Definition Client_pat u a : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Client (Some u, (Some a, tt)).

Definition D_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Disk tt.

Theorem auth_correct : forall st tr u a,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
    (KORecv PAYD COMPT COMPS (Some AC_pat)
      (Some (Build_opt_msg PAYD
        ACLoginResT (Some u, (Some a, tt)))))
    (KOExec PAYD COMPT COMPS None None (Some (Client_pat u a)))
    tr.
Admitted.

Theorem access_correct : forall st tr u a r,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
    (KORecv PAYD COMPT COMPS (Some AC_pat)
      (Some (Build_opt_msg PAYD
        ACFileResT (Some u, (Some a, (Some r, tt))))))
    (KOSend PAYD COMPT COMPS (Some D_pat)
      (Some (Build_opt_msg PAYD
        DFileReq (Some u, (Some a, (Some r, tt))))))
    tr.
Admitted.

End Spec.

Module Main := MkMain(Spec).
Import Main.