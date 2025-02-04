import FLT.Mathlib.RingTheory.LocalRing.Defs

universe u

open CategoryTheory Function
open scoped TensorProduct

namespace Deformations

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)
section IsResidueAlgebra

variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A] [IsLocalHom (algebraMap 𝓞 A)]

-- modMap : O --Under.hom-> A --IsLocalRing.residue-> k A
variable (𝓞) in
abbrev modMap : 𝓞 →+* 𝓴 A :=
   (IsLocalRing.residue A).comp (algebraMap 𝓞 A)

variable (𝓞) in
class IsResidueAlgebra : Prop where
  isSurjective : Surjective (modMap 𝓞 A)

variable [IsResidueAlgebra 𝓞 A]

variable (𝓞) in
noncomputable def IsResidueAlgebra.toRingEquiv : (𝓴 A) ≃+* (𝓴 𝓞) where
    toFun ka := IsLocalRing.residue (R := 𝓞) (surjInv (f := modMap 𝓞 A)
      (IsResidueAlgebra.isSurjective (A := A)) ka)
    invFun ko := IsLocalRing.ResidueField.lift (modMap 𝓞 A) ko
    left_inv := by
      simp [LeftInverse]
      rintro x
      rw [← RingHom.comp_apply]
      change ((IsLocalRing.residue A) ∘ (algebraMap 𝓞 A)) (surjInv _ x) = x
      rw [Function.surjInv_eq (f := (⇑(IsLocalRing.residue A) ∘ (algebraMap 𝓞 A)))]
    right_inv := by
      simp [Function.RightInverse, LeftInverse]
      rintro x
      let y := (IsLocalRing.ResidueField.lift (modMap 𝓞 A)) x
      let z := surjInv (IsResidueAlgebra.isSurjective (𝓞 := 𝓞) (A := A)) y
      let X := surjInv (IsLocalRing.residue_surjective) x
      have hX_to_x : IsLocalRing.residue 𝓞 X = x := by
        unfold X
        exact surjInv_eq (f := IsLocalRing.residue 𝓞) _ _
      have hy : y = (modMap 𝓞 A) X := by
        unfold y
        rw [← hX_to_x]
        simp
      suffices h : (IsLocalRing.residue 𝓞) z = (IsLocalRing.residue 𝓞) X by
        change (IsLocalRing.residue 𝓞) z = x
        unfold X at h
        rw [surjInv_eq (f := IsLocalRing.residue 𝓞)] at h
        exact h
      sorry
    map_mul' := by
      simp [modMap]
      rintro x y
      rw [← map_mul]
      sorry
    map_add' := by
      simp [modMap]
      rintro x y
      sorry

noncomputable instance : Algebra (𝓴 𝓞) (𝓴 A) :=
  RingHom.toAlgebra (IsResidueAlgebra.toRingEquiv 𝓞 A).symm

noncomputable instance : Algebra (𝓴 A) (𝓴 𝓞) :=
  RingHom.toAlgebra (IsResidueAlgebra.toRingEquiv 𝓞 A)

instance : RingHomInvPair
  (algebraMap (𝓴 A) (𝓴 𝓞))
  (algebraMap (𝓴 𝓞) (𝓴 A)) where
    comp_eq := sorry
    comp_eq₂ := sorry

instance : RingHomInvPair
  (algebraMap (𝓴 𝓞) (𝓴 A))
  (algebraMap (𝓴 A) (𝓴 𝓞)) where
    comp_eq := sorry
    comp_eq₂ := sorry


instance (a : Ideal A) : IsResidueAlgebra 𝓞 (A ⧸ a) :=
  sorry

end IsResidueAlgebra

end Deformations
