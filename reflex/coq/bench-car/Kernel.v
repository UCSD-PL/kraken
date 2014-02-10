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

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 10.

(*Notation "'Messages' : ms" :=
  (Definition PAYD : vvdesc _ := mk_vvdesc ms).*)

Definition PAYD := mk_vvdesc
  [
    ("Crash",   []);
    ("Acceleration",   [str_d; fd_d]);
    ("DoorsOpen",   []);
    ("UnlockDoors",   []);
    ("LockDoors", []);
    ("VolumeUp",   []);
    ("VolumeDown",   []);
    ("InflateAirbag", []);
    ("BrakesApplied", []);
    ("CruiseOff", [])
  ].

Definition Messages : list (string * (list desc)) :=
  [
    ("Crash",   []);
    ("Acceleration",   []);
    ("DoorsOpen",   []);
    ("UnlockDoors",   []);
    ("LockDoors", []);
    ("VolumeUp",   []);
    ("VolumeDown",   []);
    ("InflateAirbag", []);
    ("BrakesApplied", []);
    ("CruiseOff", [])
  ].

Inductive COMPT' : Type :=
  Engine | Brakes | CruiseCtrl | Doors | Radio | Airbag | Alarm.

Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Engine => mk_compd
                "Engine" "engine.c" []
                (mk_vdesc [])
  | Brakes => mk_compd
                "Brakes" "brakes.c" []
                (mk_vdesc [])
  | CruiseCtrl => mk_compd
                    "CruiseCtrl" "cruisectrl.c" []
                    (mk_vdesc [])
  | Doors => mk_compd
                "Doors"  "doors.c"      []
                (mk_vdesc [])
  | Radio => mk_compd
                "Radio"  "radio.c"    []
                (mk_vdesc [])
  | Airbag => mk_compd
                "Airbag" "airbag.c"  []
                (mk_vdesc [])
  | Alarm => mk_compd
                    "Alarm" "alarm.c" []
                    (mk_vdesc [])
  end.

Notation Crash        := 0%fin (only parsing).
Notation Acceleration       := 1%fin (only parsing).
Notation DoorsOpen       := 2%fin (only parsing).
Notation UnlockDoors       := 3%fin (only parsing).
Notation LockDoors       := 4%fin (only parsing).
Notation VolumeUp       := 5%fin (only parsing).
Notation VolumeDown      := 6%fin (only parsing).
Notation InflateAirbag   := 7%fin (only parsing).
Notation BrakesApplied   := 8%fin (only parsing).
Notation CruiseOff       := 9%fin (only parsing).

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Engine;
    Comp _ Brakes;
    Comp _ CruiseCtrl;
    Comp _ Doors;
    Comp _ Radio;
    Comp _ Airbag;
    Comp _ Alarm ].

Notation v_env_engine     := 0%fin (only parsing).
Notation v_env_brakes     := 1%fin (only parsing).
Notation v_env_cruisectrl := 2%fin (only parsing).
Notation v_env_doors      := 3%fin (only parsing).
Notation v_env_radio      := 4%fin (only parsing).
Notation v_env_airbag     := 5%fin (only parsing).
Notation v_env_alarm      := 6%fin (only parsing).

Definition KSTD : vcdesc COMPT := mk_vcdesc
  [ Desc _ num_d
  ; Comp _ Engine
  ; Comp _ Brakes
  ; Comp _ CruiseCtrl
  ; Comp _ Doors
  ; Comp _ Radio
  ; Comp _ Airbag
  ; Comp _ Alarm
  ].

Notation v_st_crashed       := 0%fin (only parsing).
Notation v_st_engine        := 1%fin (only parsing).
Notation v_st_brakes        := 2%fin (only parsing).
Notation v_st_cruisectrl    := 3%fin (only parsing).
Notation v_st_doors         := 4%fin (only parsing).
Notation v_st_radio         := 5%fin (only parsing).
Notation v_st_airbag        := 6%fin (only parsing).
Notation v_st_alarm         := 7%fin (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec <: SpecInterface.

Include SystemFeatures.

Open Scope hdlr.

(*Notation "[[[ p ]]]" :=
  ([[ mk_vcdesc nil : p ]]) (at level 12).

Notation "[[[ v ;;; t ;;; p ]]]" :=
  ((fun v => [[ mk_vcdesc (cons t nil) : p ]])
    (envvar (mk_vcdesc (cons t nil)) 0%fin)).*)





(*Definition hdlr_tag_dec (h1 h2:COMPT * fin NB_MSG) : decide (h1 = h2).
decide equality.
  apply fin_eq_dec.
  apply COMPTDEC.
Defined.*)
(*refine (
  match h1 with
  | (ct1, mt1) =>
    match h2 with
    | (ct2, mt2) =>
      match COMPTDEC ct1 ct2 with
      | left H =>
        match fin_eq_dec mt1 mt2 with
        | left H => _
        | right H => _
        end
      | right H => _
      end
    end
  end).
subst ct1; subst mt1; left; auto.
intuition congruence.
intuition congruence.
Defined.*)
(*        match H1 in _ = _t return
          {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD ct _t prog_envd} ->
          
        with
        | Logic.eq_refl =>
(*          match H2 in _ = _ct return
            {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct t prog_envd}
          with
          | Logic.eq_refl => prog h
          end*)
        end*)
Print Grammar constr.
Print svec_ith.
Print sig.
SearchAbout sig.
Definition INIT :=
Init [[[
  E, B, CC, D, R, AB, A ;;;
  Comp _ Engine, Comp _ Brakes, Comp _ CruiseCtrl, Comp _ Doors, Comp _ Radio, Comp _ Airbag, Comp _ Alarm ;;; 
  v_st_crashed <- (i_nlit (num_of_nat 0)) ;;
  E <- exec (Engine, tt) ;;
  v_st_engine <- (snd E) ;;
  B <- exec (Brakes, tt) ;;
  v_st_brakes <- (snd B) ;;
  CC <- exec (CruiseCtrl, tt) ;;
  v_st_cruisectrl <- (snd CC) ;;
  D <- exec (Doors, tt) ;;
  v_st_doors <- (snd D) ;;
  R <- exec (Radio, tt) ;;
  v_st_radio <- (snd R) ;;
  AB <- exec (Airbag, tt) ;;
  v_st_airbag <- (snd AB) ;;
  A <- exec (Alarm, tt) ;;
  v_st_alarm <- (snd A)
]]].
(*(*  stupd _ _ v_st_crashed (i_nlit (num_of_nat 0)) ;;*)
(*  spawn Engine tt (fst E_env) (Logic.eq_refl _) ]]].
    (Logic.eq_ind _ _ (Logic.eq_refl _) (proj1_sig (fst E_env ))
      (proj2_sig (fst E_env ))) ]]] .*)
  stupd _ _ v_st_engine (i_envvar IENVD v_env_engine) ]]] . ;;
  ! B_env ! <- exec Brakes tt ;;
(*  spawn _ IENVD Brakes tt v_env_brakes (Logic.eq_refl _);;*)
  stupd _ IENVD v_st_brakes (i_envvar IENVD v_env_brakes);;
  ! CC_env ! <- exec CruiseCtrl tt ;;
(*  spawn _ IENVD CruiseCtrl tt v_env_cruisectrl (Logic.eq_refl _);;*)
  stupd _ IENVD v_st_cruisectrl (i_envvar IENVD v_env_cruisectrl) ]]]. ;;
  spawn _ IENVD Doors  tt v_env_doors  (Logic.eq_refl _);;
  stupd _ IENVD v_st_doors (i_envvar IENVD v_env_doors);;
  spawn _ IENVD Radio  tt v_env_radio  (Logic.eq_refl _);;
  stupd _ IENVD v_st_radio (i_envvar IENVD v_env_radio);;
  spawn _ IENVD Airbag  tt v_env_airbag  (Logic.eq_refl _);;
  stupd _ IENVD v_st_airbag (i_envvar IENVD v_env_airbag);;
  spawn _ IENVD Alarm  tt v_env_alarm  (Logic.eq_refl _);;
  stupd _ IENVD v_st_alarm (i_envvar IENVD v_env_alarm)
]]].*)

Definition hdlrs :=
  When Engine sends Acceleration do
    [[[ v1 , v2 ;;;
        (Desc _ str_d) , (Desc _ fd_d) ;;;
        send (stvar v_st_doors) Acceleration (snd v1, (snd v2, tt)) ]]].

  When Engine sends Crash do
    [[[
      send (stvar v_st_airbag) InflateAirbag tt;;
      send (stvar v_st_doors) UnlockDoors tt;;
      stupd _ _ v_st_crashed (nlit (num_of_nat 1))) ]]].

  ].
  nil).

Definition hdlrs := mk_hdlrs
  [ When Engine sends Crash do
    [[ mk_vcdesc [] :
      send (stvar v_st_airbag) InflateAirbag tt;;
      send (stvar v_st_doors) UnlockDoors tt;;
      stupd _ _ v_st_crashed (nlit (num_of_nat 1)) ]];

    When Engine sends Acceleration do
    [[ mk_vcdesc [] :
      send (stvar v_st_radio) VolumeUp tt ]];

    When Alarm sends LockDoors do
    [[ mk_vcdesc [] :
      if (eq (stvar v_st_crashed) (nlit (num_of_nat 0)))
      then send (stvar v_st_doors) LockDoors tt
      else nop
    ]]
 ].
      
Inductive uhdlr_list : list hdlr -> Prop :=
| unil : uhdlr_list nil
| ucons : forall l (h : hdlr),
  (*~List.In (CT h, MTAG h) (List.map (fun h => (CT h, MTAG h)) l) ->*)
  projT1 (bool_of_sumbool (List.in_dec hdlr_tag_dec (CT h, MTAG h) (List.map (fun h => (CT h, MTAG h)) l))) = false ->
  uhdlr_list l ->
  uhdlr_list (h::l).

Fixpoint list_from_uhdlr_list (l (ul : uhdlr_list) :=
  match ul with
  | unil => nil
  | ucons l h _ ul' => h :: list_from_uhdlr_list ul'
  end.

(*Notation "[[[ ('When' ct1 'sends' mt1 'do' p1) ; .. ; ('When' ctn 'sends' mtn 'do' pn) ]]]" := 
  (fun t ct =>
    match ct, t with
    | ct1, mt1 => p1
    ..
    | ctn, mtn => pn
    end).*)

Notation "[[[ h1 ; .. ; hn ]]]" :=
  (ucons _ h1 (*(List.in_dec hdlr_tag_dec _ _)*)(Logic.eq_refl false)  .. (ucons _ hn (Logic.eq_refl false) unil) .. ).

Notation "h ||| l" := (ucons _ h (Logic.eq_refl false) l) (at level 11, right associativity).

Eval compute in List.in_dec string_dec "" (cons "a" nil).

Eval compute in projT1
    (bool_of_sumbool
       (List.in_dec hdlr_tag_dec
          (CT
             {|
             CT := Engine;
             MTAG := 0%fin;
             prog := [[mk_vcdesc [] : nop]] |},
          MTAG
            {| CT := Engine; MTAG := 0%fin; prog := [[mk_vcdesc [] : nop]] |})
          (List.map (fun h : hdlr => (CT h, MTAG h)) nil))).

Definition test := (mk_hdlr Engine Crash [[ mk_vcdesc [] : nop ]] ) ||| unil.

Definition mk_hdlrs (l : uhdlr_list) : handlers PAYD COMPT COMPS KSTD.

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match ct as _ct, t as _t return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
     | Engine, Crash =>
       [[ mk_vcdesc [] :
           seq (send (stvar v_st_airbag) InflateAirbag tt)
          (seq (send (stvar v_st_doors) UnlockDoors tt)
               (stupd _ _ v_st_crashed (nlit (num_of_nat 1))))
       ]]
     | Engine, Acceleration =>
       [[ mk_vcdesc [] :
          send (stvar v_st_radio) VolumeUp tt
       ]]
     | Doors, DoorsOpen =>
       [[ mk_vcdesc [] :
          send (stvar v_st_radio) VolumeDown tt
       ]]
     | Alarm, LockDoors =>
       [[ mk_vcdesc [] :
          ite (eq (stvar v_st_crashed) (nlit (num_of_nat 0)))
              (
                send (stvar v_st_doors) LockDoors tt
              )
              (
                nop
              )
       ]]
     | Brakes, BrakesApplied =>
       [[ mk_vcdesc [] :
          send (stvar v_st_cruisectrl) CruiseOff tt
       ]]
     | _, _ => [[ mk_vcdesc [] : nop ]]
    end.
Close Scope hdlr.
End Spec.

Module Main := MkMain(Spec).
Import Main.
