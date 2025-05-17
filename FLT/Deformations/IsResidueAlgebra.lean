import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Logic.Function.Defs
import FLT.Mathlib.RingTheory.LocalRing.Defs
import FLT.Deformations.Lemmas

open Function IsLocalRing

variable (𝓞 : Type*)
  [CommRing 𝓞] [IsLocalRing 𝓞]

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A] [IsLocalHom (algebraMap 𝓞 A)]

/--
`IsResidueAlgebra 𝓞` indicates that `A` `[Algebra 𝓞 A]` has the same residue field as `𝓞`.
It is sufficient for the natural map 𝓞 to 𝓴 A to be surjective. The actual `≃+*` between residue
fields is given in `IsResidueAlgebra.ringEquiv`.
-/
class IsResidueAlgebra : Prop where
  isSurjective' : Surjective (algebraMap 𝓞 (𝓴 A))

namespace IsResidueAlgebra

variable [IsResidueAlgebra 𝓞 A]

omit [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma algebraMap_surjective : Surjective (algebraMap 𝓞 (𝓴 A)) := isSurjective'

lemma algebraMap_bijective : Bijective (algebraMap (𝓴 𝓞) (𝓴 A)) := by
  have hsurj1 := IsLocalRing.residue_surjective (R := 𝓞)
  have hsurj2 := IsResidueAlgebra.algebraMap_surjective 𝓞 A
  exact ⟨(algebraMap (𝓴 𝓞) (𝓴 A)).injective,
    (Function.Surjective.of_comp_iff (algebraMap (𝓴 𝓞) (𝓴 A)) hsurj1).mp hsurj2⟩

noncomputable def algEquiv : 𝓴 𝓞 ≃ₐ[𝓞] 𝓴 A :=
  .ofBijective (IsScalarTower.toAlgHom _ _ _) (algebraMap_bijective _ _)

instance : IsResidueAlgebra 𝓞 𝓞 := ⟨IsLocalRing.residue_surjective⟩

section Quotient

instance (I : Ideal A) [Nontrivial (A ⧸ I)] : IsResidueAlgebra 𝓞 (A ⧸ I) where
  isSurjective' :=
    have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
    (IsLocalRing.ResidueField.map_surjective _ Ideal.Quotient.mk_surjective).comp
      (IsResidueAlgebra.algebraMap_surjective 𝓞 A)

end Quotient

section Relative

variable {𝓞 A}
  {B : Type*} [CommRing B] [Algebra 𝓞 B] [IsLocalRing B] [IsLocalHom (algebraMap 𝓞 B)]
  [IsResidueAlgebra 𝓞 B]

omit [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] [IsLocalHom (algebraMap 𝓞 B)] [IsLocalRing A]
  [IsResidueAlgebra 𝓞 A] in
lemma of_restrictScalars [Algebra A B] [IsScalarTower 𝓞 A B]
    [IsLocalHom (algebraMap A B)] : IsResidueAlgebra A B where
  isSurjective' := by
    refine .of_comp (g := algebraMap 𝓞 A) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact IsResidueAlgebra.algebraMap_surjective _ _

end Relative

open IsLocalRing

variable {A}

omit [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma exists_sub_mem_maximalIdeal (r : A) : ∃ a, r - algebraMap 𝓞 A a ∈ maximalIdeal _ := by
  obtain ⟨a, ha⟩ := IsResidueAlgebra.algebraMap_surjective 𝓞 _ (residue _ r)
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ha.symm

noncomputable
def preimage (r : A) : 𝓞 := (exists_sub_mem_maximalIdeal 𝓞 r).choose

omit [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma preimage_spec (r : A) : r - algebraMap 𝓞 A (preimage 𝓞 r) ∈ maximalIdeal _ :=
  (exists_sub_mem_maximalIdeal 𝓞 r).choose_spec

omit [IsLocalRing 𝓞] [IsLocalHom (algebraMap 𝓞 A)] in
lemma residue_preimage (r : A) : residue _ (algebraMap _ _ (preimage 𝓞 r)) = residue _ r :=
  (Ideal.Quotient.eq.mpr (preimage_spec 𝓞 r)).symm

lemma residue_preimage_eq_iff {r : A} {a} :
    residue _ (preimage 𝓞 r) = a ↔ residue _ r = ResidueField.map (algebraMap 𝓞 A) a := by
  rw [← (IsResidueAlgebra.algebraMap_bijective 𝓞 A).1.eq_iff]
  erw [ResidueField.map_residue]
  rw [residue_preimage]
  rfl

end IsResidueAlgebra
