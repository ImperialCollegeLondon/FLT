import FLT.Mathlib.RingTheory.LocalRing.Defs

universe u

open CategoryTheory Function
open scoped TensorProduct

namespace Deformation

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable (A : Type*) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A] [IsLocalHom (algebraMap 𝓞 A)]

-- modMap : O --Under.hom-> A --IsLocalRing.residue-> k A
variable (𝓞) in
abbrev modMap : 𝓞 →+* 𝓴 A :=
   (IsLocalRing.residue A).comp (algebraMap 𝓞 A)

variable (𝓞) in
class IsResidueAlgebra : Prop where
  isSurjective : Surjective (modMap 𝓞 A)

section IsResidueAlgebra

variable [IsResidueAlgebra 𝓞 A]

noncomputable instance : Algebra (𝓴 𝓞) (𝓴 A) where
  algebraMap := IsLocalRing.ResidueField.lift (modMap 𝓞 A)
  smul ko ka := (IsLocalRing.ResidueField.lift (modMap 𝓞 A) ko) * ka
  commutes' := by
    rintro r x
    exact CommMonoid.mul_comm ..
  smul_def' := by aesop

noncomputable instance : Algebra (𝓴 A) (𝓴 𝓞) where
  algebraMap := {
    toFun := fun ka ↦ (IsLocalRing.residue (R := 𝓞)) ((surjInv (IsResidueAlgebra.isSurjective (A := A))) ka)
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    map_add' := sorry
  }
  smul ka ko := (IsLocalRing.residue (R := 𝓞)) ((surjInv (IsResidueAlgebra.isSurjective (A := A))) ka) * ko
  commutes' := by
    rintro r x
    exact CommMonoid.mul_comm ..
  smul_def' := by
    rintro r x
    rfl

variable {A} in
lemma left_inv : Function.LeftInverse (algebraMap (𝓴 𝓞) (𝓴 A)) (algebraMap (𝓴 A) (𝓴 𝓞)) := by
  simp only [LeftInverse, RingHom.coe_comp, IsLocalRing.ResidueField.lift_residue_apply,
    Function.comp_apply]
  rintro x
  rw [← RingHom.comp_apply]
  change ((IsLocalRing.residue A) ∘ (algebraMap 𝓞 A)) (surjInv _ x) = x
  rw [surjInv_eq (f := (⇑(IsLocalRing.residue A) ∘ (algebraMap 𝓞 A)))]

variable {A} in
lemma right_inv : Function.RightInverse (algebraMap (𝓴 𝓞) (𝓴 A)) (algebraMap (𝓴 A) (𝓴 𝓞)) := by
  unfold Function.RightInverse LeftInverse
  rintro x
  simp only [algebraMap, Algebra.algebraMap, RingHom.coe_comp, Function.comp_apply]
  let hinj := injective_surjInv (IsLocalRing.residue_surjective (R := 𝓞))
  rw [← hinj.eq_iff]
  sorry

variable (𝓞) in
noncomputable def IsResidueAlgebra.toRingEquiv : (𝓴 A) ≃+* (𝓴 𝓞) where
  toFun := algebraMap ..
  invFun := algebraMap ..
  left_inv := left_inv
  right_inv := right_inv
  map_mul' := by aesop
  map_add' := by aesop

instance instRingHomPair : RingHomInvPair
  (algebraMap (𝓴 A) (𝓴 𝓞))
  (algebraMap (𝓴 𝓞) (𝓴 A)) where
    comp_eq := sorry
    comp_eq₂ := sorry

instance : RingHomInvPair
  (algebraMap (𝓴 𝓞) (𝓴 A))
  (algebraMap (𝓴 A) (𝓴 𝓞)) where
    comp_eq := by simp
    comp_eq₂ := by simp

variable (a : Ideal A) in
#synth IsLocalRing (A ⧸ a)

instance (a : Ideal A) : IsResidueAlgebra 𝓞 (A ⧸ a) where
  isSurjective := by
    unfold Surjective
    rintro x
    sorry

end IsResidueAlgebra

end Deformation
