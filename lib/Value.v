Require Import Coq.Strings.String.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Bool.Bvector.
Require Import Coq.Numbers.BinNums.

Require Import Monads.Monad.
Require Import Monads.Option.

Require Import Utils.

Module Import MStr := FMapList.Make(String_as_OT).

Open Scope monad.

Inductive lvalue :=
  | LValName (var: string)
  | LValMember (base: lvalue) (member: string)
.

Inductive extern :=
  | Packet (bits: list bool)
.

Inductive value :=
| ValVoid
| ValBool (b: bool)
| ValFixedBit (width: nat) (value: Bvector width)
| ValVarBit (width: nat) (value: Bvector width)
| ValFixedInt (width: nat) (n: Z)
| ValInfInt (n: Z)
| ValString (s: string)
| ValArray (arr: list value)
| ValError (msg: string)
(* I would rather this was MStr.t value but that is not a strictly
positive definition. The difference is that [Raw.t value] is
basically list (string * value) while MStr.t value is a dependent
record { raw: MStr.Raw.t; sorted: Sorted ...} which includes a proof
that the list [raw] is sorted. *)
| ValRecord (fs: MStr.Raw.t value)
| ValBuiltinFunc (name: string) (obj: lvalue)
| ValExternFunc (name: string) (obj: lvalue)
| ValExternObj (ext: extern)
| ValHeader (value: header)
| ValHeaderStack (size: nat) (nextIndex: nat) (elements: list header)

(* unused value types from the OCAML implementation

  | VStruct of
      { fields : (string * value) list; }
  | VUnion of
      { fields : (string * value) list; }
  | VEnumField of
      { typ_name : string;
        enum_name : string; }
  | VSenumField of
      { typ_name : string;
        enum_name : string;
        v : value; }
  | VSenum of (string * value) list *)

with header := MkHeader (valid: bool) (fields: MStr.Raw.t value).

Definition updateMember (obj: value) (member: string) (val: value) : option value :=
  match obj with
  | ValRecord map =>
    let* map' := assocUpdate member val map in
    mret (ValRecord map')
  | _ => None
  end.
