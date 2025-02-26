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

lemma injective : Injective (algebraMap (𝓴 𝓞) (𝓴 A)) := RingHom.injective (algebraMap (𝓴 𝓞) (𝓴 A))

class IsResidueAlgebra : Prop where
  isSurjective : Surjective (algebraMap 𝓞 (𝓴 A))

namespace IsResidueAlgebra

variable [IsResidueAlgebra 𝓞 A]

lemma surjective : Surjective (algebraMap (𝓴 𝓞) (𝓴 A)) := by
  have hsurj1 := (IsLocalRing.residue_surjective (R := 𝓞))
  have hsurj2 := IsResidueAlgebra.isSurjective (𝓞 := 𝓞) (A := A)
  exact (Function.Surjective.of_comp_iff (algebraMap (𝓴 𝓞) (𝓴 A)) hsurj1).mp hsurj2

noncomputable def ringEquiv : (𝓴 𝓞) ≃+* (𝓴 A) := RingEquiv.ofBijective
  (algebraMap (𝓴 𝓞) (𝓴 A)) ⟨injective 𝓞 A, surjective 𝓞 A⟩

section Quotient

variable {A} in
omit [IsLocalRing A] in
lemma Ideal.neq_top_of_nontrivial_quotient (I : Ideal A) [nontrivial : Nontrivial (A ⧸ I)] : I ≠ ⊤ := by
  by_contra hc
  have hsubsing := Ideal.Quotient.subsingleton_iff.mpr hc
  exact false_of_nontrivial_of_subsingleton (A ⧸ I)

variable {A} in
def residue_of_quot (I : Ideal A) [nontrivial : Nontrivial (A ⧸ I)] : (𝓴 A) →+* 𝓴 (A ⧸ I) :=
  Ideal.quotientMap (IsLocalRing.maximalIdeal (A ⧸ I)) (Ideal.Quotient.mk I) (by
    rw [← Ideal.map_le_iff_le_comap]
    suffices h : Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal A) ≠ ⊤ by
      exact IsLocalRing.le_maximalIdeal h
    rw [Ideal.ne_top_iff_one]
    by_contra hcontra
    have h := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I) (Ideal.Quotient.mk_surjective)).mp hcontra
    let x := h.choose
    have hu1 : ¬ IsUnit (x) := h.choose_spec.1
    have hu2 : IsUnit (1 - x) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits x h.choose_spec.1
    have h1minusx : 1 - x ∈ I := (Submodule.Quotient.eq I).mp (id (Eq.symm h.choose_spec.2))
    have hIneqTop : I ≠ ⊤ := Ideal.neq_top_of_nontrivial_quotient I
    have hIA : I ≤ IsLocalRing.maximalIdeal A := IsLocalRing.le_maximalIdeal hIneqTop
    have hInonUnits (x : A) (h : x ∈ I) : ¬ IsUnit x := fun _ ↦ hIA h1minusx hu2
    exact (hInonUnits (1 - x) h1minusx) hu2
  )

variable {A} in
lemma residue_of_quot_surjective (I : Ideal A) [Nontrivial (A ⧸ I)] : Surjective (residue_of_quot I) :=
  Ideal.quotientMap_surjective (Ideal.Quotient.mk_surjective)

instance (I : Ideal A) [Nontrivial (A ⧸ I)] : IsResidueAlgebra 𝓞 (A ⧸ I) where
  isSurjective := by
    have h : (residue_of_quot I) ∘ (algebraMap 𝓞 (𝓴 A)) = algebraMap 𝓞 (𝓴 (A ⧸ I)) := by
      aesop
    rw [← h]
    exact Function.Surjective.comp (residue_of_quot_surjective I) (IsResidueAlgebra.isSurjective (A := A))

end Quotient

section Relative

variable {𝓞 A}
  {B : Type*} [CommRing B] [Algebra 𝓞 B] [IsLocalRing B] [IsLocalHom (algebraMap 𝓞 B)] [IsResidueAlgebra 𝓞 B]

omit [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] [IsLocalHom (algebraMap 𝓞 B)] in
lemma of_restrictScalars [Algebra A B] [isScalarTower : IsScalarTower 𝓞 A B]
    [isLocalHom : IsLocalHom (algebraMap A B)] : IsResidueAlgebra A B where
  isSurjective := by
    have h : algebraMap A (𝓴 B) = (algebraMap (𝓴 A) (𝓴 B)) ∘ (IsLocalRing.residue A) := by aesop
    rw [h]
    have hsurj1 : Surjective (algebraMap (𝓴 A) (𝓴 B)) := by
      have hcomp : (algebraMap (𝓴 A) (𝓴 B)) ∘ (algebraMap 𝓞 (𝓴 A)) = (algebraMap 𝓞 (𝓴 B)) := by
        have : (algebraMap A (𝓴 A)) ∘ algebraMap 𝓞 A = algebraMap 𝓞 (𝓴 A) := by aesop
        rw [← this]
        have : (algebraMap B (𝓴 B)) ∘ (algebraMap A B) = (algebraMap A (𝓴 B)) := by
          ext x
          simp only [comp_apply, Algebra.algebraMap_eq_smul_one, one_smul]
          aesop
        have : (algebraMap A (𝓴 B)) ∘ algebraMap 𝓞 A = algebraMap 𝓞 (𝓴 B) := by
          ext x
          simp [comp_apply, Algebra.algebraMap_eq_smul_one, one_smul]
        aesop
      have hsurj11 : Surjective (algebraMap 𝓞 (𝓴 A)) := IsResidueAlgebra.isSurjective
      have hsurj12 : Surjective (algebraMap 𝓞 (𝓴 B)) := IsResidueAlgebra.isSurjective
      rw [← hcomp] at hsurj12
      exact (Surjective.of_comp_iff (algebraMap (𝓴 A) (𝓴 B)) hsurj11).mp hsurj12
    have hsurj2 : Surjective (IsLocalRing.residue A) := (IsLocalRing.residue_surjective (R := A))
    exact Function.Surjective.comp hsurj1 hsurj2

end Relative

end IsResidueAlgebra

end Deformation
