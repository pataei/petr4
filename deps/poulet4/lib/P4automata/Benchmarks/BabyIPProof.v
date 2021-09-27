Require Import Poulet4.P4automata.Benchmarks.ProofHeader.
Require Import Poulet4.P4automata.Benchmarks.BabyIP.
Require Import Poulet4.P4automata.CompileConfRel.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.FirstOrderConfRel.
Require Import Coq.Program.Equality.
Require Import Poulet4.P4automata.CompileConfRelSimplified.
Require Import Poulet4.P4automata.CompileFirstOrderConfRelSimplified.

Require Import Poulet4.P4automata.Sum.

From Hammer Require Import Tactics.

Notation H := (BabyIP1.header + BabyIP2.header).
Notation A := BabyIP.aut.
Notation conf := (P4automaton.configuration (P4A.interp A)).
Definition r_states :=
  Eval vm_compute in (Reachability.reachable_states
                        BabyIP.aut
                        200
                        BabyIP1.Start
                        BabyIP2.Start).

Definition top : Relations.rel conf := fun _ _ => True.
            

Ltac extend_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: ~interp_entailment A i ({| e_prem := R; e_concl := C |}));
    [ idtac |
    pose (t := WP.wp r_states C);
    eapply PreBisimulationExtend with (H0 := right H) (W := t);
    [ tauto | trivial |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t]
  end.

Ltac skip_bisim :=
  match goal with
  | |- pre_bisimulation ?a ?wp ?i ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A i ({| e_prem := R; e_concl := C |}));
    eapply PreBisimulationSkip with (H0:=left H);
    [ exact I | ];
    clear H
  end.

Ltac extend_bisim' HN := 
  match goal with
  | |- pre_bisimulation ?a _ _ _ (?C :: _) _ _ =>
    pose (t := WP.wp r_states C);
    eapply PreBisimulationExtend with (H0 := right HN) (W := t);
    [ tauto | trivial |];
    vm_compute in t;
    simpl (_ ++ _);
    clear t;
    clear HN
  end.

Ltac skip_bisim' H :=
  eapply PreBisimulationSkip with (H0:=left H);
  [ exact I | ];
  clear H.

Ltac size_script :=
  unfold Syntax.interp;
  autorewrite with size';
  vm_compute;
  repeat constructor.

Lemma forall_exists_demorgan: forall X P,
  (exists (x: X), ~P x) -> ~forall (x: X), P x.
Proof.
  intros.
  intro.
  destruct H.
  specialize (H0 x).
  contradiction.
Qed.

Declare ML Module "mirrorsolve".

RegisterPrim (@TVar (sig A) (CEmp _) (Bits 0)) "p4a.core.var".
RegisterPrim (@TFun (sig A) (CEmp _) [] (Bits 0)) "p4a.core.fun".


RegisterPrim (@FEq (sig A) (CEmp _) (Bits 0)) "p4a.core.eq".
RegisterPrim (@FTrue (sig A) (CEmp _)) "p4a.core.tt".
RegisterPrim (@FFalse (sig A) (CEmp _)) "p4a.core.ff".
RegisterPrim (@FRel (sig A) (CEmp _)) "p4a.core.rel".
RegisterPrim (@FNeg (sig A) (CEmp _)) "p4a.core.neg".
RegisterPrim (@FOr (sig A) (CEmp _)) "p4a.core.or".
RegisterPrim (@FAnd (sig A) (CEmp _)) "p4a.core.and".
RegisterPrim (@FForall (sig A) (CEmp _)) "p4a.core.forall".

RegisterPrim (@FImpl (sig A) (CEmp _)) "p4a.core.impl".

RegisterPrim (@CEmp (sig A)) "p4a.core.cnil".
RegisterPrim (@CSnoc (sig A)) "p4a.core.csnoc".

RegisterPrim (@inl BabyIP1.state bool) "p4a.core.inl".
RegisterPrim (@inr BabyIP1.state bool) "p4a.core.inr".


RegisterPrim FOBV.Bits "p4a.sorts.bits".

RegisterPrim (@TSCons (sig A) (CEmp _) (Bits 0) []) "p4a.core.tscons".
RegisterPrim (@TSNil (sig A) (CEmp _)) "p4a.core.tsnil".

Ltac crunch_foterm := 
  repeat (
    simpl || 
    simpl_eqs ||
    unfold compile_fm, compile_config, compile_conf_rel, quantify_all, quantify, compile_simplified_entailment, compile_simplified_entailment, compile_simplified_conf_rel, outer_ctx, se_st, se_prems ||
    unfold e_concl, e_prem, simplify_crel, simplify_conf_rel, cr_ctx, compile_bctx, cr_st, cs_st1, cs_st2, st_state, st_buf_len, reindex_tm, compile_store_ctx, FinType.enum, compile_store_ctx_partial || 
    autorewrite with compile_store_rel ||
    autorewrite with quantify' || 
    autorewrite with compile_bit_expr 
  ).
  

Ltac verify_interp :=
  match goal with
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A top ({| e_prem := R; e_concl := C |}));
    [
      eapply simplify_entailment_correct with (i := fun _ _ => True);
      eapply compile_simplified_entailment_correct; [
        eapply Sum.S_finite; [eapply BabyIP1.state_finite | eapply BabyIP2.state_finite] |
        eapply Sum.H_finite; [eapply BabyIP1.header_finite' | eapply BabyIP2.header_finite'] | 
        eapply compile_simplified_fm_bv_correct; [eapply Sum.S_finite; [eapply BabyIP1.state_finite | eapply BabyIP2.state_finite] |]
      ];
      
      crunch_foterm;

      match goal with 
      | |- ?X => check_interp_pos X; admit
      end
    |]
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A top ({| e_prem := R; e_concl := C |}));
    [
      eapply simplify_entailment_correct with (i := fun _ _ => True);
      eapply compile_simplified_entailment_correct; [
        eapply Sum.S_finite; [eapply BabyIP1.state_finite | eapply BabyIP2.state_finite] |
        eapply Sum.H_finite; [eapply BabyIP1.header_finite' | eapply BabyIP2.header_finite'] | 
        eapply compile_simplified_fm_bv_correct; [eapply Sum.S_finite; [eapply BabyIP1.state_finite | eapply BabyIP2.state_finite] |]
      ];
      
      


      crunch_foterm;

      match goal with 
      | |- ?X => check_interp_neg X; admit
      end
    |]; 
    clear H; 
    let H := fresh "HN" in
    assert (H: ~ (interp_entailment A top ({| e_prem := R; e_concl := C |}))) by admit
  end.

Ltac run_bisim :=
  verify_interp; 
  match goal with
  | HN: ~ (interp_entailment _ _ _ ) |- _ => 
    idtac "extending"; extend_bisim' HN; clear HN
  | H: interp_entailment _ _ _  |- _ => 
    idtac "skipping"; skip_bisim' H; clear H
  end.


Lemma prebisim_babyip:
  pre_bisimulation
    A
    (WP.wp r_states)
    top
    []
    (mk_init _ _ _ A 10 BabyIP1.Start BabyIP2.Start)
    (P4automaton.MkConfiguration
      (Syntax.interp A)
      (inl (inl BabyIP1.Start))
      0
      tt
      ltac:(eapply cap')
      nil)
    (P4automaton.MkConfiguration
      (Syntax.interp BabyIP.aut)
      (inl (inr BabyIP2.Start))
      0
      tt
      ltac:(eapply cap')
      nil).
Proof.
  idtac "running babyip bisimulation".
  set (rel0 := (mk_init _ _ _ BabyIP.aut 10 BabyIP1.Start BabyIP2.Start)).
  cbv in rel0.
  subst rel0.

  Transparent compile_fm.
  Transparent compile_store_ctx_partial.

  (* If you crunch it down without compiling, you get something that looks unsat: *)
  match goal with 
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A top ({| e_prem := R; e_concl := C |}));
    [
      eapply simplify_entailment_correct with (i := fun _ _ => True)
    |]
  end.

  unfold simplify_entailment.
  unfold e_concl, e_prem.

  unfold simplify_crel.
  simpl.
  unfold simplify_conf_rel.
  simpl.

  unfold interp_simplified_entailment.
  intros.
  simpl.
  unfold interp_simplified_conf_rel.
  simpl.
  Transparent interp_simplified_crel.
  unfold interp_simplified_crel in H2.
  simpl in H2.
  intros.
  autorewrite with interp_store_rel.
  unfold state_template_sane in *.
  simpl in *.

  (* This looks pretty unsat to me. *)

  admit.
  clear H.

  match goal with 
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A top ({| e_prem := R; e_concl := C |}));
    [
      eapply simplify_entailment_correct with (i := fun _ _ => True);
      eapply compile_simplified_entailment_correct; [
        eapply Sum.S_finite; [eapply BabyIP1.state_finite | eapply BabyIP2.state_finite] |
        eapply Sum.H_finite; [eapply BabyIP1.header_finite' | eapply BabyIP2.header_finite'] | 
        eapply compile_simplified_fm_bv_correct; [eapply Sum.S_finite; [eapply BabyIP1.state_finite | eapply BabyIP2.state_finite] |]
      ];
      
      crunch_foterm
    |]
  end.

  repeat (
    intros || 
    autorewrite with interp_fm
  ).

  (* Whereas this is a contradiction... *)
  exact H.

  clear H.



  run_bisim.
  run_bisim.
  run_bisim.
  run_bisim.
  eapply PreBisimulationClose; admit.
  (* Run this to see the FOBV syntax: *)
  (* match goal with 
  | |- pre_bisimulation ?a ?wp _ ?R (?C :: _) _ _ =>
    let H := fresh "H" in
    assert (H: interp_entailment A top ({| e_prem := R; e_concl := C |}));
    [
      eapply simplify_entailment_correct with (i := fun _ _ => True);
      eapply compile_simplified_entailment_correct; [
        eapply Sum.S_finite; [eapply BabyIP1.state_finite | eapply BabyIP2.state_finite] |
        eapply Sum.H_finite; [eapply BabyIP1.header_finite' | eapply BabyIP2.header_finite'] | 
        eapply compile_simplified_fm_bv_correct; [eapply Sum.S_finite; [eapply BabyIP1.state_finite | eapply BabyIP2.state_finite] |]
      ];
      
      crunch_foterm
    |]
  end. *)

  (* Here is the old BabyIP proof: *)

  (* extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  extend_bisim'; [admit|].
  skip_bisim'; [admit|].
  skip_bisim'; [admit|].
  skip_bisim'; [admit|].
  apply PreBisimulationClose.
  cbn.
  rewrite compile_conf_rel_correct.
  unfold compile_conf_rel.
  autorewrite with interp_fm; simpl.
  autorewrite with mod_fns; simpl;
  split.
  - left.
    easy.
  - rewrite compile_conf_rel_correct.
    unfold compile_conf_rel, FImpl; simpl.
    autorewrite with interp_fm; simpl.
    autorewrite with mod_fns; simpl. *)
Admitted.
