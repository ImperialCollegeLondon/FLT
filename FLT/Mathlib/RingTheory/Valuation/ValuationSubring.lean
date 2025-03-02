import Mathlib.RingTheory.Valuation.ValuationSubring

variable {F : Type*} [Field F]

@[simp]
lemma ValuationSubring.subtype_apply {R : ValuationSubring F} (x : R) :
    R.subtype x = x :=
  rfl

lemma ValuationSubring.subtype_injective (R : ValuationSubring F) :
    Function.Injective R.subtype :=
  (Set.injective_codRestrict Subtype.property).mp (fun ⦃_ _⦄ a ↦ a)

@[simp]
lemma ValuationSubring.subtype_inj {R : ValuationSubring F} {x y : R} :
    R.subtype x = R.subtype y ↔ x = y :=
  R.subtype_injective.eq_iff
