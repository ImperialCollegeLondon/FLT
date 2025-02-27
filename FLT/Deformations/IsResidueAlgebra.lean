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

noncomputable def ringEquiv : (𝓴 𝓞) ≃+* (𝓴 A) := RingEquiv.ofBijective
  (algebraMap (𝓴 𝓞) (𝓴 A)) ⟨(algebraMap (𝓴 𝓞) (𝓴 A)).injective, surjective 𝓞 A⟩

section Quotient

variable {A} in
omit [IsLocalRing A] in
lemma Ideal.neq_top_of_nontrivial_quotient (I : Ideal A) [nontrivial : Nontrivial (A ⧸ I)] : I ≠ ⊤ :=
  Ideal.Quotient.zero_ne_one_iff.mp zero_ne_one

lemma _Ideal.Quotient.isLocalHom_mk {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) [nontrivial : Nontrivial (A ⧸ I)] : IsLocalHom (Ideal.Quotient.mk I) where
  map_nonunit a h_fa_unit := by
    by_contra h_a_nonUnit
    obtain ⟨⟨fa, fa_inv, h_fa, h_fa_inv⟩, h_fa_eq⟩ := h_fa_unit
    simp at h_fa_eq
    rw [h_fa_eq] at h_fa h_fa_inv
    induction fa_inv using Quotient.inductionOn with
    | h b =>
      obtain ⟨i, h_iI, h_i⟩ : ∃ i ∈ I, a * b = 1 + i := by
        sorry
      obtain ⟨⟨oi, oi_inv, h_oi, h_oi_inv⟩, h_oi_eq⟩ : IsUnit (1 + i) := by
        sorry
      simp at h_oi_eq
      rw [h_oi_eq] at h_oi h_oi_inv
      let ainv := b * oi_inv
      have h_a : a * ainv = 1 := by
        unfold ainv
        rw [← mul_assoc, h_i, h_oi]
      have h_ainv : ainv * a = 1 := by
        unfold ainv
        rw [mul_comm, ← mul_assoc, h_i, h_oi]
      have : IsUnit a := ⟨⟨a, ainv, h_a, h_ainv⟩, rfl⟩
      exact h_a_nonUnit this

variable {A} in
def residue_of_quot (I : Ideal A) [nontrivial : Nontrivial (A ⧸ I)] : (𝓴 A) →+* 𝓴 (A ⧸ I) :=
  Ideal.quotientMap (IsLocalRing.maximalIdeal (A ⧸ I)) (Ideal.Quotient.mk I) (by
    rw [← Ideal.map_le_iff_le_comap]
    apply IsLocalRing.le_maximalIdeal
    rw [Ideal.ne_top_iff_one]
    by_contra hcontra
    obtain ⟨x, hx1, hx2⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I) (Ideal.Quotient.mk_surjective)).mp hcontra
    have hu1 : ¬ IsUnit x := hx1
    have hu2 : IsUnit (1 - x) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits x hx1
    have h1minusx : 1 - x ∈ I := (Submodule.Quotient.eq I).mp (id (Eq.symm hx2))
    have hIneqTop : I ≠ ⊤ := Ideal.neq_top_of_nontrivial_quotient I
    have hIA : I ≤ IsLocalRing.maximalIdeal A := IsLocalRing.le_maximalIdeal hIneqTop
    have hInonUnits (x : A) (h : x ∈ I) : ¬ IsUnit x := fun _ ↦ hIA h1minusx hu2
    exact (hInonUnits (1 - x) h1minusx) hu2
  )

variable {A} in
lemma residue_of_quot_surjective (I : Ideal A) [Nontrivial (A ⧸ I)] : Surjective (residue_of_quot I) :=
  Ideal.quotientMap_surjective (Ideal.Quotient.mk_surjective)

instance (I : Ideal A) [Nontrivial (A ⧸ I)] : IsResidueAlgebra 𝓞 (A ⧸ I) where
  isSurjective' := by
    have h : (residue_of_quot I) ∘ (algebraMap 𝓞 (𝓴 A)) = algebraMap 𝓞 (𝓴 (A ⧸ I)) := by
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
        have : (algebraMap B (𝓴 B)) ∘ (algebraMap A B) = (algebraMap A (𝓴 B)) := by
          ext x
          simp only [comp_apply, Algebra.algebraMap_eq_smul_one, one_smul]
          aesop
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
