Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexVec.
Require Import ReflexHVec.
Require Import ReflexFrontend.

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

Notation LoginReq  := (None) (only parsing).
Notation LoginResT := (Some None) (only parsing).
Notation LoginResF := (Some (Some None)) (only parsing).
Notation PubkeyReq :=      (Some (Some (Some None))) (only parsing).
Notation PubkeyRes :=      (Some (Some (Some (Some None)))) (only parsing).
Notation KeysignReq :=     (Some (Some (Some (Some (Some None))))) (only parsing).
Notation KeysignRes :=     (Some (Some (Some (Some (Some (Some None)))))) (only parsing).
Notation CreatePtyerReq := (Some (Some (Some (Some (Some (Some (Some None))))))) (only parsing).
Notation CreatePtyerRes := (Some (Some (Some (Some (Some (Some (Some (Some None)))))))) (only parsing).
Notation SLoginReq :=      (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))) (only parsing).
Notation SLoginResT :=     (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))) (only parsing).
Notation SLoginResF :=     (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))) (only parsing).
Notation SPubkeyReq :=     (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))) (only parsing).
Notation SPubkeyRes :=     (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))) (only parsing).
Notation SKeysignReq :=    (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))) (only parsing).
Notation SKeysignRes :=    (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))))) (only parsing).
Notation SCreatePtyerReq := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None)))))))))))))))) (only parsing).
Notation SCreatePtyerRes := (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some None))))))))))))))))) (only parsing).

Definition IENVD : vdesc := mk_vdesc
  [ fd_d (* system *)
  ; fd_d (* slave *)
  ].

Notation v_env_system := (None) (only parsing).
Notation v_env_slave := (Some None) (only parsing).

Definition KSTD : vdesc := mk_vdesc
  [ fd_d (* system *)
  ; fd_d (* slave *)
  ; num_d (* authenticated *)
  ; str_d (* authenticated username *)
  ].

Notation v_st_system := (None) (only parsing).
Notation v_st_slave := (Some None) (only parsing).
Notation v_st_authenticated := (Some (Some None)) (only parsing).
Notation v_st_auth_user := (Some (Some (Some None))) (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec : SpecInterface.

Module FEATURES := SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  [ fun s => spawn IENVD _ System (str_of_string "System", tt) v_env_system (Logic.eq_refl _)
  ; fun s => spawn IENVD _ Slave  tt                           v_env_slave  (Logic.eq_refl _)
  ].

Definition system_pat := (Some (str_of_string "System"), tt).

Definition exists_comp := exists_comp COMPT COMPTDEC COMPS.

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  (fun m f =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with

    | LoginReq => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         let (loginstr, _) := pl in
         (fun st0 =>
            [ fun s => send envd _ (stvar v_st_system) SLoginReq (slit loginstr, tt)
            ]
         )
       )

    | SLoginResT => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         let (user, _) := pl in
         (fun st0 =>
            if exists_comp
                 (Build_comp_pat COMPT COMPS System (Some f) system_pat)
                 (kcs _ _ _ _ st0)
            then
            [ fun s => stupd envd _ v_st_auth_user     (slit user)
            ; fun s => stupd envd _ v_st_authenticated (nlit (num_of_nat 1))
            ; fun s => send  envd _ (stvar v_st_slave) LoginResT tt
            ]
            else []
         )
       )

    | SLoginResF => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 =>
            [ fun s => send envd _ (stvar v_st_slave) LoginResF tt
            ]
         )
       )

    | PubkeyReq => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 =>
            [ fun s => send envd _ (stvar v_st_system) SPubkeyReq tt
            ]
         )
       )

    | SPubkeyRes => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         let (pubkey, _) := pl in
         (fun st0 =>
            [ fun s => send envd _ (stvar v_st_system) SPubkeyRes (slit pubkey, tt)
            ]
         )
       )

    | KeysignReq => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         let (keystr, _) := pl in
         (fun st0 =>
            [ fun s => send envd _ (stvar v_st_system) SKeysignReq (slit keystr, tt)
            ]
         )
       )

    | SKeysignRes => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         let (signedkey, _) := pl in
         (fun st0 =>
            [ fun s => send envd _ (stvar v_st_system) KeysignRes (slit signedkey, tt)
            ]
         )
       )

    | CreatePtyerReq => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 =>
           if num_eq
                (shvec_ith _ (projT2 KSTD:svec desc 4) (kst _ _ _ _ st0) v_st_authenticated)
                (num_of_nat 0)
           then []
           else [ fun s => send envd _ (stvar v_st_system) SCreatePtyerReq (stvar v_st_auth_user, tt)
                ]
         )
       )

    | SCreatePtyerRes => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         match pl with
         | (fd0, (fd1, _)) =>
           (fun st0 =>
              [ fun s => send envd _ (stvar v_st_system) CreatePtyerRes (cfd, (cfd, tt))
              ]
           )
         end
       )

       (* not meant to be received by the kernel *)
    | LoginResT => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 => [])
       )
    | LoginResF => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 => [])
       )
    | PubkeyRes => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 => [])
       )
    | KeysignRes => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 => [])
       )
    | CreatePtyerRes => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 => [])
       )
    | SLoginReq => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 => [])
       )
    | SPubkeyReq => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 => [])
       )
    | SKeysignReq => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 => [])
       )
    | SCreatePtyerReq => fun pl =>
       let envd := mk_vdesc [] in
       existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
         (fun st0 => [])
       )
    | (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some (Some bad)))))))))))))))))) => fun _ =>
      match bad with end
    end (pay PAYD m)
  ).

End Spec.

Module Main := MkMain(Spec).
Import Main.
