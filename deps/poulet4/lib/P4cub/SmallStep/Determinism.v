Require Import Poulet4.Utils.Util.Envn Poulet4.P4cub.SmallStep.Value
        Poulet4.P4cub.Syntax.Syntax Poulet4.P4cub.SmallStep.Semantics.
Import String.
Import AllCubNotations Step F.FieldTactics.

Section Determinism.
  Context {tags_t : Type}.

  Section Lemmas.
    Hint Rewrite Forall_app : core.
    Hint Rewrite (@F.predfs_data_map string) : core.
    Hint Rewrite map_app : core.
    Local Hint Extern 0 => inv_Forall_cons : core.

    Lemma step_value_false : forall ϵ (e e' : Expr.e tags_t),
      ℵ ϵ, e -->  e' -> ~ value e.
    Proof.
      intros ϵ e e' He Hv; induction He; inv Hv;
      repeat subst_term; autorewrite with core in *;
      intuition; unravel in *; auto 3.
    Qed.
  End Lemmas.

  Ltac step_value :=
    match goal with
    | He : (ℵ _, ?e -->  _), Hv : (value ?e)
      |- _ => apply step_value_false in He; contradiction
    | He : (ℵ _, ?e -->  _)
      |- ~ value ?e => apply step_value_false in He; assumption
    end.
  (**[]*)

  Local Hint Extern 0 => solve_eqn : core.

  Section ExprDeterminism.
    Local Hint Extern 0 => step_value : core.

    Ltac ind_case :=
      match goal with
      | H1: (ℵ ?ϵ, ?e -->  ?e1), H2: (ℵ ?ϵ, ?e -->  ?e2),
        IH: (forall _, ℵ ?ϵ, ?e -->  _ -> ?e1 = _)
        |- _ => apply IH in H2; inv H2
      end.
    (**[]*)

    Local Hint Extern 0 => ind_case : core.
    Local Hint Extern 0 => contradiction : core.

    Theorem expr_deterministic : forall ϵ (e e1 e2 : Expr.e tags_t),
        ℵ ϵ, e -->  e1 -> ℵ ϵ, e -->  e2 -> e1 = e2.
    Proof.
      intros ϵ e e1 e2 He1; generalize dependent e2;
      induction He1; intros e2' He2'; inv He2';
      f_equal; auto 2; subst; repeat subst_term.
      - (*assert (~ value e) by auto 1.
        assert (~ value e0) by auto 1.
        eapply Forall_until_eq in H0 as [? [? ?]]; eauto 1; subst.
        repeat f_equal; auto 2. *) admit.
      - unfold F.predfs_data, F.predf_data in *.
        (*assert (~ (value ∘ snd ∘ snd) (x, (τ, e))) by (unravel; auto 1).
        assert (~ (value ∘ snd ∘ snd) (x0, (τ0, e0))) by (unravel; auto 1).
        eapply Forall_until_eq in H0 as [? [? ?]]; eauto 1; subst.
        repeat f_equal; inv_eq; auto 2. *) admit.
      - unfold F.predfs_data, F.predf_data in *.
        (*assert (~ (value ∘ snd ∘ snd) (x, e)) by (unravel; auto 1).
        assert (~ (value ∘ snd ∘ snd) (x0, e0)) by (unravel; auto 1).
        eapply Forall_until_eq in H1 as [? ?]; eauto 1; subst.
        repeat f_equal; inv_eq; auto 2.
        admit. admit. admit. admit. admit. admit. admit. admit.*) admit.
      - assert (~ value e) by auto 1.
        assert (~ value e0) by auto 1.
        eapply Forall_until_eq in H1 as [? [? ?]]; eauto 1; subst.
        repeat f_equal; auto 2.
    Admitted.
  End ExprDeterminism.

  Lemma lvalue_deterministic : forall (e e1 e2 : Expr.e tags_t),
      ℶ e -->  e1 -> ℶ e -->  e2 -> e1 = e2.
  Proof.
    intros e e1 e2 H1; generalize dependent e2;
    induction H1; intros e2 H2; inv H2; f_equal; auto 2.
  Qed.
  Section ParserExprDeterminism.
    Local Hint Extern 0 => step_value : core.
    Local Hint Resolve expr_deterministic : core.
    Hint Rewrite Forall_app : core.
    Local Hint Extern 0 => inv_Forall_cons : core.

    Lemma parser_expr_deterministic :
      forall ϵ (e e1 e2 : AST.Parser.e tags_t),
        π ϵ, e -->  e1 -> π ϵ, e -->  e2 -> e1 = e2.
    Proof.
      intros ϵ e e1 e2 He1; generalize dependent e2;
      induction He1; intros e2 He2;
      inv He2; f_equal; repeat subst_term;
      autorewrite with core in *; intuition; unravel in *; eauto 2.
    Qed.
  End ParserExprDeterminism.
End Determinism.
