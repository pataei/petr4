Require Coq.Lists.List.
Require Import String.
Require Import HAList.
Require Poulet4.P4cub.Envn.
Require Poulet4.P4cub.BigStep.BSUtil.
Require Poulet4.P4automata.P4automaton.
Module P4A := P4automaton.

Module Env := Poulet4.P4cub.Envn.Env.

Open Scope list_scope.

Inductive hdr_ref: Type :=
| HRVar (var: string).
(*| HRField (hdr: hdr_ref) (field: string).*)

Inductive expr :=
| EHdr (h: hdr_ref)
| ELit (bs: list bool).
(* todo: binops, ...? *)

Inductive state_name: Type := 
| SNName (s: string)
| SNStart.

Definition state_ref: Type := state_name + bool.
    
Inductive v :=
| VBits : list bool -> v.

Definition v_eq_dec (v1 v2: v) : {v1 = v2} + {v1 <> v2}.
Proof.
  destruct v1, v2.
  destruct (List.list_eq_dec Bool.bool_dec l l0).
  - left; congruence.
  - right; congruence.
Defined.

Record sel_case: Type :=
  { sc_val: v;
    sc_st: state_ref }.

Inductive transition: Type :=
| TGoto (state: state_ref)
| TSel (cond: expr) (cases: list sel_case) (default: state_ref).

Inductive op :=
| OpNil
| OpSeq (o1 o2: op)
| OpExtract (width: nat) (hdr: hdr_ref)
| OpAsgn (lhs: hdr_ref) (rhs: expr).

Record state: Type :=
  { st_op: op;
    st_trans: transition }.

Definition t: Type :=
  Env.t state_name state.

Section Interp.
  Variable (a: t).

  Definition state_type :=
    { s: state_name | a s <> None }.
  
  Definition store := Env.t string v.
  
  Fixpoint op_size (o: op) : nat :=
    match o with
    | OpNil => 0
    | OpSeq o1 o2 =>
      op_size o1 + op_size o2
    | OpExtract width _ => width
    | OpAsgn _ _ => 0
    end.

  Definition find_state (st: state_type) : state.
  Proof.
    destruct (a (proj1_sig st)) eqn:?.
    - exact s.
    - exfalso.
      apply (proj2_sig st).
      apply Heqo.
  Defined.

  Definition size (state: state_type) : nat :=
    op_size (find_state state).(st_op).


  Variable (has_extract: forall s H, 0 < size (exist _ s H)).

  Definition assign (h: hdr_ref) (v: v) (s: store) : store :=
    match h with
    | HRVar x => Env.bind x v s
    end.

  Search (nat -> list ?A -> list ?A).

  Definition eval_expr (st: store) (e: expr) : v :=
   match e with
   | EHdr (HRVar x) =>
     match st x with
     | Some v => v
     | None => VBits nil
     end
   | ELit bs => VBits bs
   end.

  Fixpoint eval_op (st: store) (bits: list bool) (o: op) : store :=
    match o with
    | OpNil => st
    | OpSeq o1 o2 =>
      eval_op (eval_op st bits o1) bits o2
    | OpExtract width hdr =>
      assign hdr (VBits (List.firstn width bits)) st
    | OpAsgn hdr expr =>
      assign hdr (eval_expr st expr) st
    end.

  Definition update (state: state_type) (bits: list bool) (st: store) : store :=
    eval_op st bits (find_state state).(st_op).
  
  Fixpoint pre_eval_sel (st: store) (cond: v) (cases: list sel_case) (default: state_ref) : state_ref :=
    match cases with
    | c::cases =>
      if v_eq_dec cond c.(sc_val)
      then c.(sc_st)
      else pre_eval_sel st cond cases default
    | nil => default
    end.

  Definition clamp_state_name (s: state_name) : state_type + bool.
  Proof.
    destruct (a s) eqn:?.
    - left.
      exists s.
      congruence.
    - exact (inr false).
  Defined.

  Definition clamp_state_ref (s: state_ref) : state_type + bool :=
    match s with
    | inl s => clamp_state_name s
    | inr b => inr b
    end.
  
  Definition eval_sel (st: store) (cond: v) (cases: list sel_case) (default: state_ref) : state_type + bool :=
    clamp_state_ref (pre_eval_sel st cond cases default).

  Definition eval_trans (st: store) (t: transition) : state_type + bool :=
    match t with
    | TGoto state => clamp_state_ref state
    | TSel cond cases default =>
      eval_sel st (eval_expr st cond) cases default
    end.

  Definition transitions (s: state_type) (st: store) : state_type + bool :=
    eval_trans st (find_state s).(st_trans).

  Lemma cap: forall s, 0 < size s.
  Proof.
    intros.
    destruct s.
    apply has_extract.
  Qed.
  
  Definition interp (a: t) : P4A.p4automaton :=
    {| P4A.store := store;
       P4A.states := state_type;
       P4A.size := size;
       P4A.update := update;
       P4A.transitions := transitions;
       P4A.cap := cap |}.
End Interp.

Section Inline.

  Scheme Equality for state_name.

  Definition inline (pref: state_name) (suff: state_name) (auto: t) : t := 
    match auto pref with 
    | Some (Build_state op (TGoto (inl nxt))) => 
      if state_name_eq_dec nxt suff 
      then 
      let pref' := 
        match auto suff with 
        | Some suff_st => {| st_op := OpSeq op (st_op suff_st); st_trans := st_trans suff_st |}
        | None => {| st_op := op ; st_trans := TGoto (inl nxt) |}
        end in 
      @Env.bind _ _ _ _ state_name_eq_dec pref pref' auto
      else auto
    | _ => auto
    end.

  (* Lemma inline_corr : 
    forall pref suff auto (s: store), 
      let start_config : P4A.configuration (interp _ _ auto) := (SNStart, s, nil) in 
      True. *)

End Inline.
