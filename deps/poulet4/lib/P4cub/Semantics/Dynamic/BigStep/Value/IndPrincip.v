Require Import
        Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax
        Poulet4.P4cub.Syntax.CubNotations.
Import Val ValueNotations AllCubNotations.
Import String.

(** A custom induction principle for value. *)
Section ValueInduction.
  Variable P : v -> Prop.
  
  Hypothesis HVBool : forall b, P ~{ VBOOL b }~.
  
  Hypothesis HVBit : forall w n, P ~{ w VW n }~.
  
  Hypothesis HVInt : forall w n, P ~{ w VS n }~.
  
  Hypothesis HVTuple : forall vs,
      Forall P vs -> P ~{ TUPLE vs }~.
  
  Hypothesis HVStruct : forall fs,
      Field.predfs_data P fs -> P ~{ STRUCT { fs } }~.
  
  Hypothesis HVHeader : forall fs b,
      Field.predfs_data P fs -> P ~{ HDR { fs } VALID:=b }~.
  
  Hypothesis HVError : forall err, P ~{ ERROR err }~.
  
  Hypothesis HVHeaderStack : forall ts hs ni,
      Forall (Field.predfs_data P ∘ snd) hs ->
      P ~{ STACK hs:ts NEXT:=ni }~.
  
  Definition custom_value_ind : forall v' : v, P v' :=
    fix custom_value_ind (val : v) : P val :=
      let fix lind (vs : list v) : Forall P vs :=
          match vs with
          | [] => Forall_nil _
          | hv :: vs => Forall_cons _ (custom_value_ind hv) (lind vs)
          end in
      let fix fields_ind
              (flds : F.fs string v) : Field.predfs_data P flds :=
          match flds as fs return Field.predfs_data P fs with
          | [] => Forall_nil (Field.predf_data P)
          | (_, hfv) as hf :: tf =>
            Forall_cons hf (custom_value_ind hfv) (fields_ind tf)
          end in
      let fix ffind
              (fflds : list (bool * Field.fs string v))
          : Forall (Field.predfs_data P ∘ snd) fflds :=
          match fflds as ffs
                return Forall (Field.predfs_data P ∘ snd) ffs with
          | [] => Forall_nil (Field.predfs_data P ∘ snd)
          | (_, vs) as bv :: ffs => Forall_cons bv (fields_ind vs) (ffind ffs)
          end in
      match val with
      | ~{ VBOOL b }~             => HVBool b
      | ~{ w VS n }~              => HVInt w n
      | ~{ w VW n }~              => HVBit w n
      | ~{ TUPLE vs }~            => HVTuple vs (lind vs)
      | ~{ STRUCT { vs } }~       => HVStruct vs (fields_ind vs)
      | ~{ HDR { vs } VALID:=b }~ => HVHeader vs b (fields_ind vs)
      | ~{ ERROR err }~    => HVError err
      | ~{ STACK hs:ts NEXT:=ni }~
        => HVHeaderStack ts hs ni (ffind hs)
      end.
End ValueInduction.
