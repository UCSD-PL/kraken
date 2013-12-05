Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
Require Import ReflexHVec.
Require Import ReflexIO.
Require Import ReflexVec.
Require Import Misc.
Require Import Ascii.


Open Scope string_scope.

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 16.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [ 
  (*  Input -> Kernel *)
   (*(id,domain)*)
  ("TabCreate", [str_d; str_d])
   (*(id)*)
  ;("TabSwitch", [str_d])
  (*  Input -> Kernel -> (focused) Tab *)
  ;("Navigate", [str_d]) 
  ;("KeyPress", [str_d]) 
  ;("MouseClick", [str_d]) 
  (*  Kernel -> Input (id,domain) *)
  ;("AddrAdd", [str_d; str_d]) 
  (*  Tab -> Kernel -> Screen *)
  ;("RenderCompleted", [str_d]) 
  (*  Kernel -> Tab *)
  ;("RenderRequest", [str_d]) 
  (*  Tab -> Kernel *)
  ;("URLRequest", [str_d]) 
  (*  Kernel -> Tab *)
  ;("URLResponse", [fd_d]) 
  (*  Tab -> Kernel *)
  ;("SocketRequest", [str_d])
  (*  Kernel -> Tab (Sending out a socket to a CreateSocket.py process) *)
  ;("SocketResponse", [fd_d])
  (*  Tab -> Kernel *)
  ;("CookieChannelInit", [fd_d])
  (*  Kernel -> Cookie  *)
  ;("TabProcessRegister", [fd_d])
  (*  Kernel -> Input (id) *)
  ;("AddrFocus", [str_d]) 
  ;("DomainSet", [str_d])
  ].

Notation TabCreate   := 0%fin (only parsing).
Notation TabSwitch   := 1%fin (only parsing).
Notation Navigate    := 2%fin (only parsing).
Notation KeyPress    := 3%fin (only parsing).
Notation MouseClick  := 4%fin (only parsing).
Notation AddrAdd  := 5%fin (only parsing).
Notation RenderCompleted := 6%fin (only parsing).
Notation RenderRequest := 7%fin (only parsing).
Notation URLRequest := 8%fin (only parsing).
Notation URLResponse := 9%fin (only parsing).
Notation SocketRequest := 10%fin (only parsing).
Notation SocketResponse := 11%fin (only parsing).
Notation CookieChannelInit := 12%fin (only parsing).
Notation TabProcessRegister := 13%fin (only parsing).
Notation AddrFocus := 14%fin (only parsing).
Notation DomainSet := 15%fin (only parsing).

Inductive COMPT' : Set := UserInput | Output | Tab | CProc.

Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition comp_dir := "../test/quark/".
Definition create_socket := "../test/quark/common/socket_creator.py".
Definition wget := "../test/quark/common/pywget.py".

Definition COMPS (t : COMPT) : compd :=
  match t with
  | UserInput => mk_compd "UserInput" (comp_dir ++ "input/run.sh") 
                          [] (mk_vdesc [])
  | Output    => mk_compd "Output"    (comp_dir ++ "output/output.sh")
                          [] (mk_vdesc [])
  | Tab       => mk_compd "Tab"       (comp_dir ++ "tab/tab.sh")
                          [] (mk_vdesc [str_d;str_d]) (*id,domain*)
  | CProc     => mk_compd "CProc"     (comp_dir ++ "cookie/cookie.py")
                          [] (mk_vdesc [str_d])
  end.

(*
Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Output; Comp _ Tab; Comp _ UserInput ].
*)

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Output; Comp _ UserInput ].

Notation i_output    := 0%fin (only parsing).
Notation i_userinput := 1%fin (only parsing).

Definition KSTD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Output; Comp _ Tab; Comp _ UserInput ].

Notation v_output := (0%fin) (only parsing).
Notation v_curtab := (1%fin) (only parsing).
Notation v_userinput := 2%fin (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec <: SpecInterface.

Include SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  seq (spawn _ IENVD Output    tt                   i_output    (Logic.eq_refl _)) (
  seq (spawn _ IENVD UserInput tt                   i_userinput (Logic.eq_refl _)) (
  seq (stupd _ IENVD v_output (i_envvar IENVD i_output)) (
  (stupd _ IENVD v_userinput (i_envvar IENVD i_userinput))))).

Definition hdlr_tab_dom {t envd} :=
  cconf (envd:=envd) (t:=t) Tab Tab 1%fin (CComp PAYD COMPT COMPS KSTD Tab t envd).

Definition cur_tab_dom {t envd ct} :=
  cconf (envd:=envd) (t:=t) ct Tab 1%fin (StVar _ _ _ KSTD _ _ _ v_curtab).

Definition cur_tab_id {t envd ct} :=
  cconf (envd:=envd) (t:=t) ct Tab 0%fin (StVar _ _ _ KSTD _ _ _ v_curtab).

Definition dom_op {envd term} d e :=
  unop_str envd term (Desc _ str_d) (dom d) e.

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match ct as _ct, t as _t return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | UserInput, TabCreate =>
      let envd := mk_vcdesc [Comp _ Tab] in
      [[ envd :
          complkup (envd:=envd) (mk_comp_pat _ _ Tab (Some (mvar TabCreate 0%fin), (None, tt)))
                   nop
                   (seq (spawn _ envd Tab (mvar TabCreate 0%fin, (mvar TabCreate 1%fin, tt))
                               0%fin (Logic.eq_refl _))
                   (seq (send (envvar envd 0%fin) DomainSet (mvar TabCreate 1%fin, tt))
                   (seq (stupd _ envd v_curtab (envvar envd 0%fin))
                        (send (stvar v_userinput) AddrAdd
                              (mvar TabCreate 0%fin, (mvar TabCreate 1%fin, tt))))))
      ]]
  | UserInput, TabSwitch =>
      let envd := mk_vcdesc [] in
      [[ envd :
           complkup (envd:=envd)
                    (mk_comp_pat _ _ Tab
                                 (Some (mvar TabSwitch 0%fin), (None, tt)))
                    (seq (stupd _ _ v_curtab (envvar (mk_vcdesc [Comp _ Tab]) 0%fin))
                    (seq (send (stvar v_userinput) AddrFocus
                               (mvar TabSwitch 0%fin, tt))
                    (seq (send (stvar v_output) RenderCompleted (cur_tab_id, tt))
                         (send (stvar v_curtab) RenderRequest
                               (slit nil, tt)))))
                    nop
      ]]
  | UserInput, Navigate =>
      [[ mk_vcdesc [] :
           ite (eq (dom_op ("/") (mvar Navigate 0%fin)) cur_tab_dom)
               (
                 send (stvar v_curtab) Navigate (mvar Navigate 0%fin, tt)
               )
               (
                 nop
               )
     ]]
  | UserInput, KeyPress =>
      [[ mk_vcdesc [] :
           send (stvar v_curtab) KeyPress (mvar KeyPress 0%fin, tt)
      ]]
  | UserInput, MouseClick =>
      [[ mk_vcdesc [] :
           send (stvar v_curtab) MouseClick (mvar MouseClick 0%fin, tt)
      ]]
  | Tab, RenderCompleted =>
      [[ mk_vcdesc [] :
         ite (eq ccomp (stvar v_curtab))
             (
               (seq (send (stvar v_userinput) AddrFocus
                               (cur_tab_id, tt))
                    (send (stvar v_output) RenderCompleted
                          (cur_tab_id, tt)))
             )
             (
               nop
             )
       ]]
  | Tab, URLRequest =>
      let envd := mk_vcdesc [Desc _ fd_d] in
      [[ envd :
         seq (call _ envd (slit (str_of_string (wget)))
                   [mvar URLRequest 0%fin] None (Logic.eq_refl _))
             (send ccomp URLResponse (envvar envd 0%fin, tt))
       ]]
  | Tab, SocketRequest =>
    let envd := mk_vcdesc [Desc _ fd_d] in
    [[ envd :
       ite (eq (dom_op (":") (mvar SocketRequest 0%fin)) hdlr_tab_dom)
       (
         seq (call _ envd (slit (str_of_string (create_socket)))
                                [mvar SocketRequest 0%fin] 0%fin (Logic.eq_refl _))
             (send ccomp SocketResponse (envvar envd 0%fin, tt))
       )
       (
         nop
       )
    ]]
  | Tab, CookieChannelInit =>
      let envd := mk_vcdesc [Comp _ CProc] in
      let envd' := (mk_vcdesc [Comp _ CProc; Comp _ CProc]) in
      [[ envd :
        complkup (envd:=envd) (mk_comp_pat _ _ CProc (Some hdlr_tab_dom, tt))
                 (send (envvar envd' 1%fin)
                   TabProcessRegister (mvar CookieChannelInit 0%fin, tt))
                 (seq (spawn _ envd CProc (hdlr_tab_dom, tt) 0%fin
                             (Logic.eq_refl _))
                 (seq (send (envvar envd 0%fin) DomainSet (hdlr_tab_dom, tt))
                      (send (envvar envd 0%fin) TabProcessRegister
                            (mvar CookieChannelInit 0%fin, tt))))
      ]]
  | _, _ =>
    [[ mk_vcdesc [] : nop ]]
  end.
Close Scope hdlr.

End Spec.

Module Main := MkMain(Spec).
