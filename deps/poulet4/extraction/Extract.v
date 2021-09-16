Require Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNativeString.
Require Import Coq.extraction.ExtrOcamlNatInt.

Require Import Coq.Numbers.BinNums.

Extract Inductive positive => "Bigint.t"
  [ "(fun p -> (Bigint.succ (Bigint.(of_int 2 * p))))"
    "(fun p -> (Bigint.(of_int 2 *  p)))" "(Bigint.one)" ]
  "(fun f2p1 f2p f1 p -> if Bigint.(p <= one) then f1 () else let (q, r) = Bigint.(p / of_int 2, rem p (Bigint.of_int 2)) in if Bigint.equal r Bigint.zero then f2p q else f2p1 q)".

Extract Inductive Z => "Bigint.t" [ "Bigint.zero" "" "(fun z -> Bigint.neg z)" ]
  "(fun fO fp fn z -> let s = Bigint.sign z in if s = Zero then fO () else if s = Pos then fp z else fn (Bigint.neg z))".

Extract Inductive N => "Bigint.t" [ "(Bigint.zero)" "" ]
  "(fun fO fp n -> (match Bigint.sign n with | Neg -> fO () | _ -> fp n))".

Require Poulet4.SimplExpr.
Require Poulet4.GenLoc.

Extract Constant SyntaxUtil.dummy_ident => "(fun () -> failwith ""unrealized dummy_ident reached"")".
Extract Constant SimplExpr.to_digit => "(fun x -> Char.chr 20)".
Extract Constant SimplExpr.N_to_string_aux => "(fun x y z -> z)". (* Don't remove: this line informs Coq to not actually extract this function. *)
Extract Constant SimplExpr.N_to_string => "(fun x -> Z.to_string (Bigint.to_zarith_bigint x))".
Extract Constant SimplExpr.add1 => "(fun x -> Bigint.of_zarith_bigint (Z.succ (Bigint.to_zarith_bigint x)))".
Extract Inlined Constant SimplExpr.Nzero => "(Bigint.zero)".
Extract Inlined Constant BinNat.N.eqb => "Bigint.(=)".
Extract Inlined Constant BinNat.N.add => "Bigint.(+)".
Extract Inlined Constant Nat.add => "(+)".

Require Poulet4.Syntax.
Require Poulet4.Typed.
Require Poulet4.Ops.

Separate Extraction
         Coq.Classes.EquivDec
         Poulet4.Syntax
         Poulet4.Typed
         Poulet4.Ops
         Poulet4.SimplExpr
         Poulet4.GenLoc.
