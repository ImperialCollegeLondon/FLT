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

abbrev modMap_high : 𝓞 →+* 𝓴 A :=
  (IsLocalRing.residue A).comp (algebraMap 𝓞 A)

abbrev modMap : (𝓴 𝓞) →+* 𝓴 A :=
  IsLocalRing.ResidueField.map (algebraMap 𝓞 A)

lemma modMap_injective : Injective (modMap 𝓞 A) := RingHom.injective (modMap 𝓞 A)

class IsResidueAlgebra : Prop where
  isSurjective : Surjective (modMap_high 𝓞 A)

namespace IsResidueAlgebra

variable [IsResidueAlgebra 𝓞 A]

lemma modMap_surjective : Surjective (modMap 𝓞 A) := by
  have hsurj1 := (IsLocalRing.residue_surjective (R := 𝓞))
  have hsurj2 := IsResidueAlgebra.isSurjective (𝓞 := 𝓞) (A := A)
  exact (Function.Surjective.of_comp_iff (modMap 𝓞 A) hsurj1).mp hsurj2

noncomputable def ringEquiv : (𝓴 𝓞) ≃+* (𝓴 A) := RingEquiv.ofBijective
  (modMap 𝓞 A) ⟨modMap_injective 𝓞 A, modMap_surjective 𝓞 A⟩

section Quotient

variable {A} in
omit [IsLocalRing A] in
lemma Ideal.neq_top_of_nontrivial_quotient (I : Ideal A) [nontrivial : Nontrivial (A ⧸ I)] : I ≠ ⊤ := by
  by_contra hc
  have h := nontrivial.exists_pair_ne
  have hsubsing := Ideal.Quotient.subsingleton_iff.mpr hc
  rw [hc] at *
  exact h.choose_spec.choose_spec (hsubsing.allEq h.choose h.choose_spec.choose)

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
    have h : (residue_of_quot I) ∘ (modMap_high 𝓞 A) = modMap_high 𝓞 (A ⧸ I) := by
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
    letI : IsLocalHom (algebraMap A B) := isLocalHom
    have h : modMap_high A B = (modMap A B) ∘ (IsLocalRing.residue A) := by aesop
    rw [h]
    have hsurj1 : Surjective (modMap A B) := by
      have hcomp : (modMap A B) ∘ (modMap_high 𝓞 A) = (modMap_high 𝓞 B) := by
        simp only [RingHom.coe_comp]
        have : modMap A B ∘ (IsLocalRing.residue A) = (IsLocalRing.residue B) ∘ (algebraMap A B) := by
          aesop
        rw [← comp_assoc, this, comp_assoc]
        have : (algebraMap A B) ∘ algebraMap 𝓞 A = algebraMap 𝓞 B := by
          ext x
          simp [comp_apply, Algebra.algebraMap_eq_smul_one, one_smul]
        rw [this]
      have hsurj11 : Surjective (modMap_high 𝓞 A) := IsResidueAlgebra.isSurjective
      have hsurj12 : Surjective (modMap_high 𝓞 B) := IsResidueAlgebra.isSurjective
      rw [← hcomp] at hsurj12
      exact (Surjective.of_comp_iff (modMap A B) hsurj11).mp hsurj12
    have hsurj2 : Surjective (IsLocalRing.residue A) := (IsLocalRing.residue_surjective (R := A))
    exact Function.Surjective.comp hsurj1 hsurj2

end Relative

end IsResidueAlgebra

end Deformation
