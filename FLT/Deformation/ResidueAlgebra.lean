import FLT.Mathlib.RingTheory.LocalRing.Defs
import FLT.Mathlib.RingTheory.Ideal.Lattice

import Mathlib

open CategoryTheory Function
open scoped TensorProduct

universe u

namespace Deformation

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable (A : Type u) [CommRing A] [Algebra 𝓞 A] [IsLocalRing A] [IsLocalHom (algebraMap 𝓞 A)]

-- modMap : O --Under.hom-> A --IsLocalRing.residue-> k A
variable (𝓞) in
abbrev modMap_high : 𝓞 →+* 𝓴 A :=
  (IsLocalRing.residue A).comp (algebraMap 𝓞 A)

variable (𝓞) in
abbrev modMap : (𝓴 𝓞) →+* 𝓴 A :=
  IsLocalRing.ResidueField.lift (modMap_high 𝓞 A)

instance instInjective : Injective (modMap 𝓞 A) := RingHom.injective (modMap 𝓞 A)

variable (𝓞) in
class IsResidueAlgebra : Prop where
  isSurjective : Surjective (modMap_high 𝓞 A)

namespace IsResidueAlgebra

variable [IsResidueAlgebra 𝓞 A]

instance instSurjective : Surjective (modMap 𝓞 A) := by
  have hcomp : (modMap 𝓞 A) ∘ (IsLocalRing.residue (R := 𝓞)) = modMap_high 𝓞 A := by aesop
  have hsurj1 := (IsLocalRing.residue_surjective (R := 𝓞))
  have hsurj2 := IsResidueAlgebra.isSurjective (𝓞 := 𝓞) (A := A)
  unfold modMap_high at hsurj2
  refine (Function.Surjective.of_comp_iff (modMap 𝓞 A) hsurj1).mp hsurj2

variable (𝓞) in
noncomputable abbrev modMapInv' : (𝓴 A) → 𝓴 𝓞 := invFun (modMap 𝓞 A)

omit [IsNoetherianRing 𝓞] [IsResidueAlgebra 𝓞 A] in
variable (𝓞) in
lemma leftInverse : LeftInverse (modMapInv' 𝓞 A) (modMap 𝓞 A) :=
  leftInverse_invFun (instInjective A)

omit [IsNoetherianRing 𝓞] in
variable (𝓞) in
lemma rightInverse : RightInverse (modMapInv' 𝓞 A) (modMap 𝓞 A) :=
  rightInverse_invFun (instSurjective A)

variable (𝓞) in
noncomputable abbrev modMapInv : (𝓴 A) →+* 𝓴 𝓞 :=
  RingHom.inverse (modMap 𝓞 A) (modMapInv' 𝓞 A) (leftInverse 𝓞 A) (rightInverse 𝓞 A)

instance instRingHomPair : RingHomInvPair (modMap 𝓞 A) (modMapInv 𝓞 A) where
  comp_eq := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.inverse_apply, RingHom.id_apply]
    exact (leftInverse 𝓞 A) x
  comp_eq₂ := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.inverse_apply, RingHom.id_apply]
    exact (rightInverse 𝓞 A) x

variable (𝓞) in
noncomputable def ringEquiv : (𝓴 𝓞) ≃+* (𝓴 A) := .ofHomInv (modMap 𝓞 A) (modMapInv 𝓞 A)
  (by change (modMapInv _ _).comp (modMap _ _) = _; simp)
  (by change (modMap _ _).comp (modMapInv _ _) = _; simp)

instance instRingHomPair₂ : RingHomInvPair (modMapInv 𝓞 A) (modMap 𝓞 A) where
  comp_eq := by simp
  comp_eq₂ := by simp

instance (I : Ideal A) [I.NeqTop] : IsResidueAlgebra 𝓞 (A ⧸ I) where
  isSurjective := by
    simp only [Surjective, modMap, algebraMap, Algebra.algebraMap, RingHom.coe_comp,
      Function.comp_apply]
    rintro x_kai
    let x_ai := surjInv (IsLocalRing.residue_surjective) x_kai
    let x_a := surjInv (Ideal.Quotient.mk_surjective) x_ai
    let x_ka := IsLocalRing.residue A x_a
    let x_o := surjInv (IsResidueAlgebra.isSurjective (𝓞 := 𝓞) (A := A)) x_ka
    use x_o
    unfold x_o x_ka x_a x_ai
    sorry

end IsResidueAlgebra

end Deformation
