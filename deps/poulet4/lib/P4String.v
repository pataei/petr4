Require Petr4.Str.

Record t (tags_t: Type) :=
  { tags: tags_t;
    str: Str.t }.
Arguments tags [tags_t] _.
Arguments str [tags_t] _.

Definition strip [tags_t: Type] (s: t tags_t) :=
  {| tags := tt; str := s.(str) |}.

Definition equiv [tags_t: Type] (s1 s2: t tags_t) : Prop :=
  s1.(str) = s2.(str).

Definition equivb [tags_t: Type] (s1 s2: t tags_t) :=
  String.eqb s1.(str) s2.(str).

Definition eq_const [tags_t: Type] (s1: t tags_t) (s2: Str.t) :=
  Str.eqb s1.(str) s2.
