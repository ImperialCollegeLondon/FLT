import Mathlib.RingTheory.Valuation.ValuationSubring

variable {F : Type*} [Field F]

lemma ValuationSubring.subtype_inj {R : ValuationSubring F} {x y : R} :
    R.subtype x = R.subtype y ↔ x = y :=
  R.subtype_injective.eq_iff
