

 import FLT.DedekindDomain.Completion.BaseChange
 import FLT.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct
 import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module
 import FLT.Mathlib.Topology.Algebra.Algebra.Hom
 import FLT.Mathlib.LinearAlgebra.Pi
 import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib

@[expose] public section

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum adicCompletion Extension

open scoped TensorProduct -- ⊗ notation for tensor product

lemma tendsTo_comap_cofinite [FaithfulSMul A B] :
    Filter.Tendsto (under A (B:=B)) Filter.cofinite Filter.cofinite :=
  have : FaithfulSMul A (FractionRing B) := FractionRing.instFaithfulSMul A B
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <|
    Extension.finite A (FractionRing A) (FractionRing B) B)

lemma cofinite_mapsTo_adicCompletionSemialgHom :
    ∀ᶠ (w : HeightOneSpectrum B) in Filter.cofinite,
    Set.MapsTo (Extension.adicCompletionSemialgHom K L (v := under A w) ⟨w, rfl⟩)
      (adicCompletionIntegers K (under A w)) (adicCompletionIntegers L w) := by
  apply Filter.Eventually.of_forall
  intro w
  exact Set.image_subset_iff.1 <| adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨w, rfl⟩

namespace FiniteAdeleRing

@[inherit_doc]
scoped notation:max "𝔸ᶠ[" A ", " K "]" => FiniteAdeleRing A K

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields. -/
noncomputable def mapRingHom : 𝔸ᶠ[A, K] →+* 𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  RestrictedProduct.mapAlongRingHom (adicCompletion K) (adicCompletion L) (under A)
    (tendsTo_comap_cofinite A B) (fun w ↦ adicCompletionSemialgHom K L (v := w.under A) ⟨w, rfl⟩)
    (cofinite_mapsTo_adicCompletionSemialgHom A K L B)

-- /-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields,
-- as a morphism lying over the canonical map `K → L`. -/
-- noncomputable def mapSemialgHom :
--     𝔸ᶠ[A, K] →SA[algebraMap K L] 𝔸ᶠ[B, L] where
--   __ := FiniteAdeleRing.mapRingHom A K L B
--   map_smul' k a := by
--     ext w
--     simpa only [Algebra.smul_def'] using!
--       (adicCompletionSemialgHom K L (v := w.under A) ⟨w, rfl⟩).map_smul' k (a (under A w))
--   continuous_toFun :=
--     have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
--     RestrictedProduct.mapAlong_continuous _ _ _ (tendsTo_comap_cofinite A B) _
--       (cofinite_mapsTo_adicCompletionSemialgHom A K L B)
--       fun w ↦ adicCompletionSemialgHom_continuous K L ⟨w, rfl⟩


open scoped TensorProduct.RightActions RestrictedProduct

variable [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]

instance : Algebra (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, v.adicCompletionIntegers K])
    (Πʳ w: HeightOneSpectrum B, [w.adicCompletion L, w.adicCompletionIntegers L]) :=
  inferInstanceAs (Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L])

/--
error: failed to synthesize
  SMul Πʳ (b : HeightOneSpectrum A), [adicCompletion K b, ↑(adicCompletionIntegers K b)]
    Πʳ (a : HeightOneSpectrum B), [adicCompletion L a, ↑(adicCompletionIntegers L a)]
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached

Note: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
error: `sorryAx` is not a structure

Hint: This error is possibly due to a change in the `structure` syntax. Now the syntax is `structure S : Type extends P` rather than `structure S extends P : Type`.

The purpose of the change is to accommodate `structure S extends toP : P` syntax for naming parent projections.
-/
#guard_msgs in
/-- Utility class which specialises `RestrictedProduct.FiberwiseSMul` to the case of
finite adele rings. -/
class ComapFiberwiseSMul extends RestrictedProduct.FiberwiseSMul (α := HeightOneSpectrum B)
    (under A) (adicCompletion K) (fun v ↦ adicCompletionIntegers K v) Filter.cofinite
    (adicCompletion L) (fun w ↦ adicCompletionIntegers L w) Filter.cofinite

#exit
