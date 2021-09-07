Require Import Coq.Lists.List.
Import ListNotations.
Require Import Poulet4.FinType.
Require Import Poulet4.P4automata.PreBisimulationSyntax.
Require Import Poulet4.P4automata.P4automaton.
Require Import Poulet4.P4automata.FirstOrder.
Require Import Poulet4.P4automata.Ntuple.

Require Import Coq.Lists.List.

Section AutModel.
  Set Implicit Arguments.
  (* State identifiers. *)
  Variable (S: Type).
  Context `{S_eq_dec: EquivDec.EqDec S eq}.
  Context `{S_finite: @Finite S _ S_eq_dec}.

  (* Header identifiers. *)
  Variable (H: nat -> Type).
  Context `{H_eq_dec: forall n, EquivDec.EqDec (H n) eq}.
  Instance H'_eq_dec: EquivDec.EqDec (P4A.H' H) eq := P4A.H'_eq_dec (H_eq_dec:=H_eq_dec).
  Context `{H_finite: @Finite (Syntax.H' H) _ H'_eq_dec}.

  Variable (a: P4A.t S H).

  Notation conf := (configuration (P4A.interp a)).

  Inductive sorts: Type :=
  | Bits (n: nat)
  | State
  | Store
  | Key (n: nat)
  | ConfigPair (n m: nat).

  Inductive funs: arity sorts -> sorts -> Type :=
  | BitsLit: forall n, n_tuple bool n -> funs [] (Bits n)
  | KeyLit: forall n, H n -> funs [] (Key n)
  | Concat: forall n m, funs [Bits n; Bits m] (Bits (n + m))
  | Slice: forall n hi lo, funs [Bits n] (Bits (Nat.min (1 + hi) n - lo))
  | Lookup: forall n, funs [Store; Key n] (Bits n)
  | Update: forall n, funs [Store; Key n; Bits n] Store
  | State1: forall n m, funs [ConfigPair n m] State
  | Store1: forall n m, funs [ConfigPair n m] Store
  | State2: forall n m, funs [ConfigPair n m] State
  | Store2: forall n m, funs [ConfigPair n m] Store
  | Buf1: forall n m, funs [ConfigPair n m] (Bits n)
  | Buf2: forall n m, funs [ConfigPair n m] (Bits m).

  Inductive rels: arity sorts -> Type :=.

  Definition sig: signature :=
    {| sig_sorts := sorts;
       sig_funs := funs;
       sig_rels := rels |}.

  Definition fm ctx := FirstOrder.fm sig ctx.
  Definition tm ctx := FirstOrder.tm sig ctx.
  Definition tms ctx := FirstOrder.tms sig ctx.

  Definition conf' (n: nat) :=
    {c: conf | c.(conf_buf_len _) = n}.

  Definition mod_sorts (s: sig_sorts sig) : Type :=
    match s with
    | Bits n => n_tuple bool n
    | State => states (P4A.interp a) + bool
    | Store => store (P4A.interp a)
    | Key n => H n
    | ConfigPair n m => conf' n * conf' m
    end.

  Definition l2t {A} (l: list A) : n_tuple A (List.length l).
  Admitted.

  Definition n_zeroes (n: nat) : n_tuple bool n.
  Admitted.

  Notation "x ::: xs" := (HList.HCons _ x xs) (at level 60, right associativity).

  Obligation Tactic := idtac.
  Equations mod_fns
             {params ret}
             (f: sig_funs sig params ret)
             (args: HList.t mod_sorts params)
    : mod_sorts ret :=
    { mod_fns (BitsLit n xs) hnil := xs;
      mod_fns (KeyLit k) hnil := k;
      mod_fns (Concat n m) (xs ::: ys ::: hnil) :=
        n_tuple_concat xs ys;
      mod_fns (Slice n hi lo) (xs ::: hnil) :=
        n_tuple_slice hi lo xs;
      mod_fns (Lookup n) (store ::: key ::: hnil) :=
        match P4A.find H key store with
        | Some (P4A.VBits _ v) => v
        | None => n_zeroes n
        end;
      mod_fns (Update n) (store ::: k ::: v ::: hnil) :=
        P4A.assign _ k (P4A.VBits _ v) store;
      mod_fns (State1 _ _) ((q1, q2) ::: hnil) := (proj1_sig q1).(conf_state _);
      mod_fns (Store1 _ _) ((q1, q2) ::: hnil) := (proj1_sig q1).(conf_store _);
      mod_fns (State2 _ _) ((q1, q2) ::: hnil) := (proj1_sig q2).(conf_state _);
      mod_fns (Store2 _ _) ((q1, q2) ::: hnil) := (proj1_sig q2).(conf_store _);
      mod_fns (Buf1 n m) ((q1, q2) ::: hnil) := _;
      mod_fns (Buf2 n m) ((q2, q2) ::: hnil) := _
    }.
  Next Obligation.
    unfold conf'.
    intros.
    pose ((proj1_sig q1).(conf_buf _)).
    destruct q1.
    simpl in *.
    rewrite e in n0.
    exact n0.
  Defined.
  Next Obligation.
    unfold conf'.
    intros.
    pose ((proj1_sig q2).(conf_buf _)).
    destruct q2.
    simpl in *.
    rewrite e in n0.
    exact n0.
  Defined.

  Fixpoint tr_bctx (b: bctx): ctx sig :=
    match b with
    | BCEmp => CEmp _
    | BCSnoc b size => CSnoc _ (tr_bctx b) (Bits size)
    end.

  Fixpoint be_size {c} b1 b2 (e: bit_expr H c) : nat :=
    match e with
    | BELit _ _ l => List.length l
    | BEBuf _ _ side =>
      match side with
      | Left => b1
      | Right => b2
      end
    | BEHdr _ a (P4A.HRVar h) => projT1 h
    | BEVar _ x => check_bvar x
    | BESlice e hi lo =>
      Nat.min (1 + hi) (be_size b1 b2 e) - lo
    | BEConcat e1 e2 =>
      be_size b1 b2 e1 + be_size b1 b2 e2
    end.

  Definition be_sort {c} b1 b2 (e: bit_expr H c) : sorts :=
    Bits (be_size b1 b2 e).

  Equations tr_var {c: bctx} (x: bvar c) : var sig (tr_bctx c) (Bits (check_bvar x)) :=
    { tr_var (BVarTop c size) :=
        VHere sig (tr_bctx c) (Bits (check_bvar (BVarTop c size)));
      tr_var (BVarRest y) :=
        VThere sig (tr_bctx _) _ (Bits (check_bvar y)) (tr_var y) }.

  Equations tr_bit_expr {c}
    (b1 b2: nat)
    (q: tm (tr_bctx c) (ConfigPair b1 b2))
    (e: bit_expr H c)
    : tm (tr_bctx c) (be_sort b1 b2 e) :=
    { tr_bit_expr q (BELit _ _ l) :=
        TFun sig (BitsLit (List.length l) (l2t l)) TSNil;
      tr_bit_expr q (BEBuf _ _ Left) :=
        TFun sig (Buf1 b1 b2) (TSCons q TSNil);
      tr_bit_expr q (BEBuf _ _ Right) :=
        TFun sig (Buf2 b1 b2) (TSCons q TSNil);
      tr_bit_expr q (BEHdr _ Left (P4A.HRVar h)) :=
        let key := TFun sig (KeyLit (projT2 h)) TSNil in
        let store := TFun sig (Store1 b1 b2) (TSCons q TSNil) in
        TFun sig (Lookup (projT1 h)) (TSCons store (TSCons key TSNil));
      tr_bit_expr q (BEHdr _ Right (P4A.HRVar h)) :=
        let key := TFun sig (KeyLit (projT2 h)) TSNil in
        let store := TFun sig (Store2 b1 b2) (TSCons q TSNil) in
        TFun sig (Lookup (projT1 h)) (TSCons store (TSCons key TSNil));
      tr_bit_expr q (BEVar _ b) :=
        TVar (tr_var b);
      tr_bit_expr q (BESlice e hi lo) :=
        TFun sig (Slice _ hi lo) (TSCons (tr_bit_expr q e) TSNil);
      tr_bit_expr q (BEConcat e1 e2) :=
        TFun sig (Concat _ _) (TSCons (tr_bit_expr q e1) (TSCons (tr_bit_expr q e2) TSNil)) }.

End AutModel.

Section BitsBV.

  Require Import Coq.Init.Specif.
  Require Import Coq.micromega.Lia.
  Require Import SMTCoq.SMTCoq.
  Import BVList.BITVECTOR_LIST.
  Require Import Coq.NArith.BinNat.



  Inductive bv_sorts: Type :=
  | BVBits (len: {n: nat | n > 0})
  | BVBool.

  Definition pos := {n: nat | n > 0}.

  Program Definition plus (l: {n: nat | n > 0}) (r: {n: nat | n > 0}) : {n: nat | n > 0} := l + r.
  Next Obligation.
  lia.
  Defined.

  (* Definition gt (l: {n: nat | n > 0}) (r: {n: nat | n > 0})  := . *)
  
  Program Definition sub_add_one (i : nat) (j: nat) : (i >= j) -> {n: nat | n > 0} := fun pf => i - j + 1.
  Next Obligation.
  lia.
  Defined.

  Inductive bool_bop: Type := 
  | BImpl | BXor.

  Inductive bv_funs: arity bv_sorts -> bv_sorts -> Type :=
  | BoolLit: forall (b: bool), bv_funs [] BVBool
  | BVLit: forall (bv: list bool) (pf: List.length bv > 0), bv_funs [] (BVBits (exist _ (List.length bv) pf))
  | BoolBop: forall (bop: bool_bop), bv_funs [BVBool; BVBool] BVBool
  | BVConcat : forall i j, bv_funs [BVBits i; BVBits j] (BVBits (plus i j))
  | BVExtract : forall (i j: nat) (m n : {x: nat | x > 0}) (pf: i >= j),
    proj1_sig m > i -> 
    n = sub_add_one pf  ->
    bv_funs [BVBits m] (BVBits n).

  Inductive bv_rels: arity bv_sorts -> Type := .

  Definition bv_sig : signature := 
    {| sig_sorts := bv_sorts; sig_funs := bv_funs; sig_rels := bv_rels |}.

  Definition bv_mod_sorts (sig: bv_sig.(sig_sorts)) : Type := 
    match sig with 
    | BVBool => bool
    | BVBits n => bitvector (N_of_nat (proj1_sig n))
    end.

  (* inclusive slicing *)

  Definition slice {A} (hi lo: nat) (xs: list A) := firstn (hi - lo + 1) (skipn (lo - 1) xs).

  (* Compute (slice 3 2 (1::2::3::4::5::nil)). *)

  Lemma slice_len:
    forall A hi lo (xs : list A),
      List.length xs > hi -> 
      hi >= lo -> 
      List.length (slice hi lo xs) = hi - lo + 1.
  Proof.
    intros.
    induction hi; induction lo; simpl.
    - unfold slice.
      simpl.
      destruct xs; [exfalso; simpl in *; lia | simpl; trivial].
    - exfalso.
      inversion H0.
    - unfold slice.
      simpl (0 - 1).
      erewrite skipn_O.
      simpl (S hi - 0 + 1).
      erewrite firstn_length.

      eapply min_l.
      lia.

    - admit.
  Admitted.

  Notation "x ::: xs" := (HList.HCons _ x xs) (at level 60, right associativity).

  Require Import Coq.NArith.Nnat.

  Definition bv_concat' {x y} (l: bv_mod_sorts (BVBits x)) (r: bv_mod_sorts (BVBits y)) : bv_mod_sorts (BVBits (plus x y)).
  unfold plus.
  simpl in *.
  erewrite Nat2N.inj_add.
  exact (bv_concat l r).
  Defined.
  

  Equations bv_mod_fns {args: arity (sig_sorts bv_sig)} {ret: sig_sorts bv_sig} 
    (sf: bv_sig.(sig_funs) args ret) 
    (env: HList.t bv_mod_sorts args) : bv_mod_sorts ret := {
      bv_mod_fns (BoolLit b) _ := b;
      bv_mod_fns (BVLit bv _) _ := of_bits bv;
      bv_mod_fns (BoolBop op) (l ::: r ::: _) := 
        match op with 
        | BImpl => implb l r
        | BXor => xorb l r
        end;
      (* I'm not sure why but the arguments of BVExtract are bound to a bunch of sf* variables *)
      bv_mod_fns (BVExtract _ _ _) (x ::: _) := @bv_extr (N.of_nat (proj1_sig sf1)) (N.of_nat (proj1_sig sf2)) (N.of_nat (proj1_sig sf1)) x;
      bv_mod_fns (BVConcat _ _) (l ::: r ::: _) := bv_concat' l r
  }.

  

  (* Definition bv_mod_fns' {args: arity (sig_sorts bv_sig)} {ret: sig_sorts bv_sig} 
    (sf: bv_sig.(sig_funs) args ret) 
    (env: HList.t bv_mod_sorts args) : bv_mod_sorts ret.
  destruct sf eqn:?.
  - (* Boolean literal case *)
    exact b.
  - (* Bitvector literal case *)
    simpl. 
    eapply (exist _ bv).
    trivial.
  - (* Boolean binop case *)
    inversion env.
    simpl in X.
    clear env H0 a H1 rest.
    inversion X0.
    simpl in X1.
    clear H0 H1 X0 rest X2 a.
    destruct bop eqn:?.
    * exact (implb X X1).
    * exact (xorb X X1).
  - (* Bitvector concatenation case *)
    inversion env.
    simpl in X.
    clear env H0 a H1 rest.
    inversion X0.
    simpl in X1.
    clear H0 H1 X0 rest X2 a.

    destruct X.
    destruct X1.

    eapply (exist _ (x ++ x0)).

    simpl.
  
    rewrite <- e.
    rewrite <- e0.

    eapply app_length.
  - (* Bitvector extract binop case *)
    rewrite e.
    simpl.

    inversion env.
    simpl in X.
    clear env H0 a H1 rest X0.

    destruct X.

    eapply (exist _ (slice i j x)).

    eapply slice_len; lia.
  Defined. *)

  Definition bv_mod_rels {args}
    (sig_args: bv_sig.(sig_rels) args) 
    (env: HList.t bv_mod_sorts args) : Prop := False.

  Definition bv_model : model bv_sig.
  refine {| FirstOrder.mod_sorts := bv_mod_sorts; 
       FirstOrder.mod_fns := _; FirstOrder.mod_rels := _ |}.

  - intros. 
    exact (bv_mod_fns H X).
  - intros.
    exact (bv_mod_rels X X0).
  Defined.

  (* true = true *)

  (* Universe inconsistency error here...
  Definition ex0 : fm (@CEmp bv_sig).
  refine (
    FEq _ (CEmp _) _ _ _
  ).
  - refine (TFun _ _ _ _ _ _).
    * refine (BoolLit true).
    * constructor.
  - refine (TFun _ _ _ _ _ _).
    * refine (BoolLit true).
    * constructor.
  Defined.

  (* Equations ex0' : fm bv_sig (CEmp _) := {
    ex0' := FEq _ (CEmp _) _ (TFun _ _ _ _ (BoolLit true) _) (TFun _ _ _ _ (BoolLit true) _)
  }. *)

  (* Transparent interp_fm. *)

  (* Print Rewrite HintDb interp_fm. *)

  Lemma ex0_interp : interp_fm bv_sig bv_model (CEmp _) (VEmp _ _) ex0.
  Proof.
    unfold ex0.
    autorewrite with interp_fm bv_mod_fns.
    simpl.
    smt_uncheck; admit.
  Admitted.
  

  (* forall x, x -> x *)

  Definition ex1 : fm bv_sig (CEmp _).
  refine (
    FForall _ (CEmp _) _ _
  ).
  refine (
    FEq _ _ _ _ _
  ).
  - refine (TFun _ _ _ _ _ _).
    * refine (BoolBop BImpl).
    * repeat constructor;  refine (TVar _ _ _ _); constructor.
  - refine (TFun _ _ _ _ _ _).
    * refine (BoolLit true).
    * constructor.
  Defined.

  Lemma ex1_interp : interp_fm bv_sig bv_model (CEmp _) (VEmp _ _) ex1.
  Proof.
    unfold ex1.
    autorewrite with interp_fm.
    intros.
    autorewrite with interp_fm bv_mod_fns find.
    simpl in *. (* we need this to reduce the hypothesis' type to bool, otherwise smtcoq breaks*)
    smt_uncheck; admit.
    (* confusingly, vm_compute reduces to an if-then-else, which is not recognized by smtcoq *)
  Admitted.

  (* forall a b c, (a -> b) -> (b -> c) -> (a -> c) *)

  (* Definition ex2 : fm bv_sig (CEmp _).
  refine (
    FForall _ (CEmp _) _ _
  ).
  refine (
    FForall _ _ _ _
  ).
  refine (
    FForall _ _ _ _
  ).
  refine (
    FEq _ _ _ _ _
  ).
  - refine (TFun _ _ _ _ _ _).
    * refine (BoolBop BImpl).
    * constructor.
      + refine (TFun _ _ _ _ _ _).

  - refine (TFun _ _ _ _ _ _).
    * refine (BoolLit true).
    * constructor.
  Defined. *)



  *)
End BitsBV.
