Require Import Monads.Monad.
Require Import Monads.State.
Require Import Monads.P4Monad.
Require Import Monads.Hoare.WP.
Open Scope monad.
Require Import Lists.List.
Import ListNotations.
Require Import Program.

Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Plus.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.Lists.List.
Require Import Equations.Equations.

Notation REmp := HAList.REmp.
Notation RCons := HAList.RCons.

Definition IPHeader :=
  HAList.t
    [("src", bits 8);
     ("dst", bits 8);
     ("proto", bits 4)].

Definition IPHeader_p : PktParser IPHeader :=
  let* src := extract_n 8 in 
  let* dst := extract_n 8 in 
  let* proto := extract_n 4 in 
  state_return (RCons src (RCons dst (RCons proto REmp))).

Definition TCP :=
  HAList.t
  [("sport", bits 8);
   ("dport", bits 8);
   ("flags", bits 4);
   ("seq", bits 8)].

Definition TCP_p : PktParser TCP :=
  let* sport := extract_n 8 in 
  let* dport := extract_n 8 in 
  let* flags := extract_n 4 in 
  let* seq := extract_n 8 in 
    state_return (RCons sport (RCons dport (RCons flags (RCons seq REmp)))).

Definition UDP := 
  HAList.t
  [("sport", bits 8); 
   ("dport", bits 8);
   ("flags", bits 4)].

Definition UDP_p : PktParser UDP :=
  let* sport := extract_n 8 in 
  let* dport := extract_n 8 in 
  let* flags := extract_n 4 in 
    state_return (RCons sport (RCons dport (RCons flags REmp))).

Definition Headers := 
  HAList.t
  [("ip", IPHeader); 
   ("transport", (TCP + UDP)%type)].

Definition Headers_p : PktParser Headers := 
  let* iph := IPHeader_p in 
  let proto := HAList.get iph (exist _ "proto" I) in
  match proto with 
  | (false, (false, (false, (false, tt)))) =>
    let* tcp := TCP_p in 
      state_return (RCons iph (RCons (inl tcp) REmp))
  | (false, (false, (false, (true, tt)))) =>
    let* udp := UDP_p in 
      state_return (RCons iph (RCons (inr udp) REmp))
  | _ => reject
  end.

Lemma Header_destruct (h: Headers) : 
  exists ip trans, h = RCons ip (RCons trans REmp).
Proof.
  unfold Headers in *.
  dependent destruction h.
  dependent destruction h.
  dependent destruction h.
  eauto.
Qed.

Definition MyIngress (hdr: Headers) : PktParser Headers := 
  match HAList.get hdr (exist _ "transport" I) with 
  | inl _ => 
    set_std_meta (fun mt => HAList.set mt (exist _ "egress_spec" I) one_bits) ;; state_return hdr 
  | _ => 
    set_std_meta (fun mt => HAList.set mt (exist _ "egress_spec" I) zero_bits) ;; state_return hdr 
  end.

Definition MyProg (pkt: list bool) : PktParser Headers :=
  put_state (fun _ => init_state pkt) ;;
  let* hdr := Headers_p in 
    MyIngress hdr.

Definition HeaderWF (pkt : list bool) : Prop :=
  (List.nth_error pkt 16 = Some false) /\
  (List.nth_error pkt 17 = Some false) /\
  (List.nth_error pkt 18 = Some false) /\
  ((List.nth_error pkt 19 = Some false /\ length pkt = 40) \/
    (List.nth_error pkt 19 = Some true /\ length pkt = 32)).

Definition IPHeaderIsTCP (pkt : list bool) : Prop :=
  length pkt = 40 /\ List.nth_error pkt 19 = Some true.

Definition IPHeaderIsUDP (pkt : list bool) : Prop :=
  length pkt = 32 /\ List.nth_error pkt 19 = Some false.

Definition EgressSpecOne (out : @ParserState Meta) : Prop :=
  HAList.get (std_meta out) (exist _ "egress_spec" I) = one_bits.

Definition EgressSpecZero (out : @ParserState Meta) : Prop :=
  HAList.get (std_meta out) (exist _ "egress_spec" I) = zero_bits.

Definition PacketConsumed (out : @ParserState Meta) : Prop :=
  match pkt out with
  | nil => True
  | _ => False
  end.

Ltac app_ex := 
  intros; repeat match goal with 
  | [ H : _ |- _ ] => exact H 
  | [ H : (_ /\ _)%type |- _] => destruct H
  | [ H : (exists _, _)%type |- _] => destruct H
  end.

Ltac wp_trans :=
  intros; match goal with
  | [ |- << _ >> mbind _ _ << _ >> ] => eapply bind_wp_p; try wp_trans
  | [ |- << _ >> get_state << _ >> ] => eapply get_wp_p || eapply strengthen_pre_p; try eapply get_wp_p
  | [ |- << _ >> put_state ?e << _ >> ] => eapply (put_wp_p e) || eapply strengthen_pre_p; try eapply (put_wp_p e)
  | [ |- << _ >> state_fail ?e << _ >> ] => eapply (fail_wp_p e) || eapply strengthen_pre_p; try eapply (fail_wp_p e)
  | [ |- << _ >> state_return ?e << _ >> ] => eapply (return_wp_p e) || eapply strengthen_pre_p; try eapply (return_wp_p e)
  | [ |- << _ >> if _ then _ else _ << _ >> ] => eapply cond_wp_p; eapply strengthen_pre_p; try wp_trans
  | [ |- << _ >> match ?e with | 0 => _ | S _ => _ end << _ >> ] => eapply (case_nat_wp_p e); eapply strengthen_pre_p; try wp_trans
  | [ |- << _ >> match ?e with | nil => _ | _ :: _ => _ end << _ >> ] =>
    eapply (case_list_wp_p e);
    try wp_trans
  | [ |- << _ >> match ?e with | Some _ => _ | None => _ end << _ >> ] =>
    eapply (case_option_wp_p e);
    try wp_trans
  | [ |- << _ >> match ?e with | inl _ => _ | _ => _ end << _ >> ] =>
    eapply (case_sum_wp_p e);
    try wp_trans
  end.

Ltac break_match :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ] =>
    destruct e eqn:?
  end.

Lemma update_override:
  forall (s: @ParserState Meta) b b',
    s <| pkt := b |> <| pkt := b' |> = s <| pkt := b' |>
.
Proof.
  intros.
  destruct s.
  reflexivity.
Qed.

Lemma update_noop:
  forall (s: @ParserState Meta),
    s <| pkt := pkt s |> = s
.
Proof.
  intros.
  destruct s.
  reflexivity.
Qed.

Lemma next_bit_spec :
  forall s b,
  << fun s0 => s <| pkt := b :: pkt s |> = s0 >>
    next_bit
  << fun r s1 => s1 = s /\ r = b >>
.
Proof.
  intros.
  unfold next_bit, reject.
  eapply strengthen_pre_p.
  wp_trans; try app_ex.
  simpl.
  intros.
  break_match.
  - exfalso. 
    rewrite <- H in Heql.
    simpl in Heql.
    discriminate.
  - rewrite <- H in Heql.
    simpl in Heql.
    inversion Heql.
    split.
    + rewrite <- H.
      rewrite update_override.
      apply update_noop.
    + reflexivity.
Qed.

Lemma next_bit_sp s': 
  << fun s => s = s' /\ length (pkt s) > 0 >>
    next_bit
  << fun r s => 
    s' = s <| pkt := r :: (pkt s) |>
  >>.
Proof.
    unfold next_bit.
    eapply strengthen_pre_p.
    unfold reject.
    wp_trans; try app_ex.
    simpl. intros.
    destruct H.
    destruct h.
    destruct pkt.
    all: simpl in *.
    unfold bot.
    lia.
    rewrite <- H.
    simpl.
    trivial.
Qed.

Definition extract_bit_wp' {Q} := 
  build_wp next_bit 
    (fun s => length (pkt s) > 0) 
    Q 
    (fun s => match pkt s with | [] => (true, s) | b :: bs => (b, s <| pkt := bs |> ) end).

Lemma extract_bit_wp_corr : 
  forall Q, @extract_bit_wp' Q.
Proof.

  eapply build_wp_corr.
  intros.
  eapply hoare_consequence_p.
  eapply (next_bit_sp s).
  all: simpl; intros.
  - destruct H. split; auto.
  - destruct s.
    unfold set. simpl in *.
    inversion H.
    split; trivial.
    destruct h.
    simpl. trivial.
Qed.

Lemma frame_wp_p:
  forall {State Exception Result}
         (P: State -> Prop)
         (prog: @state_monad State Exception Result)
         (Q: Result -> State -> Prop)
         (H: Prop),
    (H -> << P >> prog << Q >>)
    ->
    << fun s => P s /\ H >>
      prog
    << fun r s => Q r s /\ H >>
.
Proof.
  unfold hoare_partial_wp.
  intros.
  destruct H1.
  specialize (H0 H2 st H1).
  destruct (prog st).
  destruct s.
  - split; eauto.
  - eauto.
Qed.

Lemma extract_n_nice :
  forall n s bits,
  << fun s0 => s0 = s <| pkt := bits2list bits ++ pkt s |> >>
    extract_n n
  << fun r s1 => s1 = s /\ r = bits >>
.
Proof.
  induction n; intros.
  - unfold extract_n, reject.
    wp_trans; try app_ex.
    simpl.
    rewrite H.
    destruct bits.
    split.
    + apply update_noop.
    + reflexivity.
  - unfold extract_n.
    fold extract_n.
    destruct bits.
    wp_trans; try app_ex; simpl.
    + eapply strengthen_pre_p.
      * apply next_bit_spec.
      * simpl; intros.
        now rewrite H, update_override.
    + simpl.
      eapply weaken_post_p.
      eapply frame_wp_p.
      * intros.
        eapply strengthen_pre_p.
        apply IHn.
        simpl; intros.
        exact H0.
      * simpl; intros.
        destruct H, H.
        now rewrite H0, H1.
Qed.

Ltac mylen ls := 
  match ls with 
  | _ :: ?tl => 
    let l' := mylen tl in 
    constr:(S l')
  | _ => 0
  end.

Ltac myinduct l := destruct l; (simpl; try (exfalso; simpl in *; lia)).

Lemma extract_bit_wp {Q} : 
  << fun s => 
    match (pkt s) with 
    | [] => False
    | b :: bs => Q b (s <| pkt := bs |> )
    end
  >> next_bit << Q >>.
Proof.
  unfold next_bit, reject.
  eapply strengthen_pre_p.
  wp_trans; try app_ex.
  simpl. intros.
  destruct h.
  destruct pkt.
  - unfold set in H. simpl in *. trivial.
  - unfold set in H. simpl in *. trivial.
Qed.

Lemma extract_n_wp n {Q: Post ParserState (bits n)}: 
  << fun s => 
    n <= length (pkt s) /\ 
    exists (bts: bits n) suff,
    pkt s = (bits2list bts) ++ suff /\
    Q bts (s <| pkt := suff |>)
  >> 
    extract_n n 
  << Q >>.
Proof.
  induction n.
  - unfold extract_n, reject.
    wp_trans. simpl. intros.
    destruct H.
    destruct h.
    destruct pkt.
    * simpl in *.
      destruct H0.
      destruct H0.
      destruct H0.
      rewrite <- H0 in H1.
      unfold set in H1. simpl in H1.
      destruct x.
      trivial.
    * simpl in *.
      destruct H0.
      destruct H0.
      destruct H0.
      rewrite <- H0 in H1.
      unfold set in H1. simpl in H1.
      destruct x.
      trivial.
  - unfold extract_n. fold extract_n. unfold reject.
    eapply strengthen_pre_p.
    wp_trans; try app_ex.
    Check extract_bit_wp'.
    all: swap 2 1.
    eapply IHn.
    eapply extract_bit_wp_corr.
    simpl. intros.
    destruct (pkt h).
    + destruct H. simpl in H. lia.
    + split.
      * intros.
        simpl.
        lia.
      * intros. destruct H.
        split; simpl in *; try lia.
        destruct H0.
        destruct x.
        exists p.
        destruct H0.
        exists x.
        simpl in H0.
        destruct H0.
        inversion H0.
        split; trivial.
Qed.


Lemma IPHeader_p_spec st: 
  << fun s => s = st /\ length (pkt s) >= 20 >>
    IPHeader_p
  << fun r s' => 
    s' = st <| pkt := skipn 20 (pkt st) |> 
  >>.
Proof.
  unfold IPHeader_p, reject.
  wp_trans.
  4: app_ex.
  3: eapply (extract_n_wp 4).
  2: eapply (extract_n_wp 8).
  eapply strengthen_pre_p.
  eapply (extract_n_wp 8).
  intros.
  simpl.
  destruct H.
  rewrite <- H.
  myinduct (pkt h).
  do 19 (myinduct l).
  intros.
  split; [lia|].
  exists (list2bits [b; b0; b1; b2; b3; b4; b5; b6]).
  exists ([b7; b8; b9; b10; b11; b12; b13; b14; b15; b16; b17; b18] ++ l).
  simpl.
  split.
   - trivial.
   - split; [lia|].
    exists (list2bits [b7; b8; b9; b10; b11; b12; b13; b14]).
    exists ([b15; b16; b17; b18] ++ l).
    simpl. split; [trivial|].
    split; intros; [lia|].
    exists(list2bits [b15; b16; b17; b18]).
    exists l.
    simpl. split; [trivial|].
    erewrite update_override.
    erewrite update_override.
    trivial.
Qed.

Lemma TCP_p_spec st: 
  << fun s => s = st /\ length (pkt s) >= 28 >>
    TCP_p
  << fun r s' => 
    s' = st <| pkt := skipn 28 (pkt st) |> 
  >>.
Proof.
  unfold TCP_p.
Admitted.

Lemma UDP_p_spec st: 
  << fun s => s = st /\ length (pkt s) >= 20 >>
    UDP_p
  << fun r s' => 
    s' = st <| pkt := skipn 20 (pkt st) |> 
  >>.
Admitted.

Lemma ParseTCPCorrect pckt :
  << fun s => pkt s = pckt /\ HeaderWF (pkt s) /\ IPHeaderIsTCP (pkt s) >>
    MyProg pckt
  << fun _ s => EgressSpecZero s >>.
Proof.
  unfold MyProg.
  unfold Headers_p.
  unfold reject.
  wp_trans.
  all: swap 4 1.
  unfold MyIngress.
  intros.
  wp_trans.
  unfold HAList.get.
  inversion r0.
  inversion X.
  assert (HAList.get_k r0
  (projT2
     (HAList.get_key_type
        (HAList.mk_key
           (exist
              (fun k1 : string =>
               HAList.alist_In k1
                 [("ip", IPHeader); ("transport", (TCP + UDP)%type)])
              "transport" I)))) = x0).
              admit.

  rewrite H.
  destruct x0; unfold set_std_meta; wp_trans; try app_ex.
  all: swap 2 1.
  intros.
  inversion r0.
  inversion X.
  inversion X0.
  assert (x1 = HAList.get r0
  (exist
     (fun k2 : string =>
      HAList.alist_In k2
        [("src", bits 8); ("dst", bits 8); ("proto", bits 4)])
     "proto" I)).
     admit.
  rewrite <- H.
  destruct x1.
  eapply strengthen_pre_p.
  wp_trans; try app_ex.
  destruct p.
  eapply strengthen_pre_p.
  wp_trans; try app_ex.
  destruct p.
  eapply strengthen_pre_p.
  wp_trans; try app_ex.
  destruct p.
  eapply strengthen_pre_p.
  wp_trans; try app_ex.
  destruct p.
  eapply strengthen_pre_p.
  wp_trans; try app_ex.
  eapply weaken_post_p.
  eapply UDP_p_spec.
  intros.
  assert ((HAList.get (RCons r0 (RCons (inr v) REmp))
  (exist
     (fun k2 : string =>
      HAList.alist_In k2
        [("ip", IPHeader); ("transport", (TCP + UDP)%type)]) "transport" I)) = inr v).
  admit.
  destruct ((HAList.get (RCons r0 (RCons (inr v) REmp))
  (exist
     (fun k2 : string =>
      HAList.alist_In k2
        [("ip", IPHeader); ("transport", (TCP + UDP)%type)]) "transport" _))).
  exfalso. inversion H10.

  unfold EgressSpecZero.
  autorewrite with get_k.
  assert ((HAList.get
  (std_meta
     (s <| std_meta ::=
      (fun mt : StandardMeta =>
       HAList.set mt
         (exist
            (fun k2 : string =>
             HAList.alist_In k2
               [("egress_spec", bits 9)])
            "egress_spec" I) zero_bits)
      |>))
  (exist
     (fun k2 : string =>
      HAList.alist_In k2
        [("egress_spec", bits 9)])
     "egress_spec" I)) = @zero_bits 9).
     admit.
  exact H11.
  intros.
  apply H9.
  

  all: swap 6 1.
  eapply IPHeader_p_spec.
  all: swap 5 1.
  destruct p.
  wp_trans.
  eapply TCP_p_spec.
  intros.
Admitted. 

Lemma ParseUDPCorrect pckt :
  << fun s => pkt s = pckt /\ HeaderWF (pkt s) /\ IPHeaderIsUDP (pkt s) >>
    MyProg pckt
  << fun _ s => EgressSpecOne s >>.
Admitted.

Theorem ParseComplete pckt : 
  << fun s => 
    pkt s = pckt /\ 
    HeaderWF (pkt s) /\ 
    (IPHeaderIsUDP (pkt s) \/ IPHeaderIsTCP (pkt s))
  >>
    MyProg pckt
  << fun _ s' => PacketConsumed s' >>.
Admitted.
