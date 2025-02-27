import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Logic.Function.Defs
import FLT.Mathlib.RingTheory.LocalRing.Defs

open Function
open scoped TensorProduct

namespace Deformation

variable (𝓞 : Type*)
  [CommRing 𝓞] [IsLocalRing 𝓞]

local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A] [IsLocalHom (algebraMap 𝓞 A)]

/--!
  `IsResidueAlgebra 𝓞` indicates that `A` `[Algebra 𝓞 A]` has the same residue field as `𝓞`.
  It is sufficient for the natural map 𝓞 to 𝓴 A to be surjective. The actual `≃+*` between residue
  fields is given in `IsResidueAlgebra.ringEquiv`.
--/
class IsResidueAlgebra : Prop where
  isSurjective' : Surjective (algebraMap 𝓞 (𝓴 A))

namespace IsResidueAlgebra

variable [IsResidueAlgebra 𝓞 A]

omit [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma isSurjective : Surjective (algebraMap 𝓞 (𝓴 A)) := isSurjective'

lemma surjective : Surjective (algebraMap (𝓴 𝓞) (𝓴 A)) := by
  have hsurj1 := IsLocalRing.residue_surjective (R := 𝓞)
  have hsurj2 := IsResidueAlgebra.isSurjective 𝓞 A
  exact (Function.Surjective.of_comp_iff (algebraMap (𝓴 𝓞) (𝓴 A)) hsurj1).mp hsurj2

/--!
  Ring equivalence between the residue field of `𝓞` and `A`, when `[IsResidueAlgebra 𝓞 A]`
--/
noncomputable def ringEquiv : (𝓴 𝓞) ≃+* (𝓴 A) := RingEquiv.ofBijective
  (algebraMap (𝓴 𝓞) (𝓴 A)) ⟨(algebraMap (𝓴 𝓞) (𝓴 A)).injective, surjective 𝓞 A⟩

section Quotient

variable {A} in
omit [IsLocalRing A] in
lemma Ideal.neq_top_of_nontrivial_quotient (I : Ideal A) [nontrivial : Nontrivial (A ⧸ I)] : I ≠ ⊤ :=
  Ideal.Quotient.zero_ne_one_iff.mp zero_ne_one

variable {A} in
lemma residue_of_quot_surjective (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Surjective (algebraMap (𝓴 A) (𝓴 (A ⧸ I))) := by
  change Surjective (Ideal.quotientMap _ _ (by
    intro nu hnu
    have : ¬IsUnit (Ideal.Quotient.mk I nu) := by
      by_contra hfnu
      exact hnu ((IsLocalHom.quotient_mk I).map_nonunit nu hfnu)
    aesop
  ))
  exact Ideal.quotientMap_surjective (Ideal.Quotient.mk_surjective)

instance (I : Ideal A) [Nontrivial (A ⧸ I)] : IsResidueAlgebra 𝓞 (A ⧸ I) where
  isSurjective' := by
    have h : (algebraMap (𝓴 A) (𝓴 (A ⧸ I))) ∘ (algebraMap 𝓞 (𝓴 A)) = algebraMap 𝓞 (𝓴 (A ⧸ I)) := by
      aesop
    rw [← h]
    exact Function.Surjective.comp (residue_of_quot_surjective I)
      (IsResidueAlgebra.isSurjective 𝓞 A)

end Quotient

section Relative

variable {𝓞 A}
  {B : Type*} [CommRing B] [Algebra 𝓞 B] [IsLocalRing B] [IsLocalHom (algebraMap 𝓞 B)] [IsResidueAlgebra 𝓞 B]

omit [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] [IsLocalHom (algebraMap 𝓞 B)] in
lemma of_restrictScalars [Algebra A B] [isScalarTower : IsScalarTower 𝓞 A B]
    [isLocalHom : IsLocalHom (algebraMap A B)] : IsResidueAlgebra A B where
  isSurjective' := by
    have h : algebraMap A (𝓴 B) = (algebraMap (𝓴 A) (𝓴 B)) ∘ (IsLocalRing.residue A) := by aesop
    rw [h]
    have hsurj1 : Surjective (algebraMap (𝓴 A) (𝓴 B)) := by
      have hcomp : (algebraMap (𝓴 A) (𝓴 B)) ∘ (algebraMap 𝓞 (𝓴 A)) = (algebraMap 𝓞 (𝓴 B)) := by
        have : (algebraMap A (𝓴 A)) ∘ algebraMap 𝓞 A = algebraMap 𝓞 (𝓴 A) := by aesop
        rw [← this]
        have : (algebraMap A (𝓴 B)) ∘ algebraMap 𝓞 A = algebraMap 𝓞 (𝓴 B) := by
          ext x
          simp [comp_apply, Algebra.algebraMap_eq_smul_one, one_smul]
        aesop
      have hsurj11 : Surjective (algebraMap 𝓞 (𝓴 A)) := IsResidueAlgebra.isSurjective 𝓞 A
      have hsurj12 : Surjective (algebraMap 𝓞 (𝓴 B)) := IsResidueAlgebra.isSurjective 𝓞 B
      rw [← hcomp] at hsurj12
      exact (Surjective.of_comp_iff (algebraMap (𝓴 A) (𝓴 B)) hsurj11).mp hsurj12
    have hsurj2 : Surjective (IsLocalRing.residue A) := (IsLocalRing.residue_surjective (R := A))
    exact Function.Surjective.comp hsurj1 hsurj2

end Relative

end IsResidueAlgebra

end Deformation
