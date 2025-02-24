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
  have hcomp : (modMap 𝓞 A) ∘ (IsLocalRing.residue (R := 𝓞)) = modMap_high 𝓞 A := by aesop
  have hsurj1 := (IsLocalRing.residue_surjective (R := 𝓞))
  have hsurj2 := IsResidueAlgebra.isSurjective (𝓞 := 𝓞) (A := A)
  exact (Function.Surjective.of_comp_iff (modMap 𝓞 A) hsurj1).mp hsurj2

noncomputable def ringEquiv : (𝓴 𝓞) ≃+* (𝓴 A) := RingEquiv.ofBijective
  (modMap 𝓞 A) ⟨modMap_injective 𝓞 A, modMap_surjective 𝓞 A⟩

instance ringHomInvPair₁ : RingHomInvPair (ringEquiv 𝓞 A).toRingHom (ringEquiv 𝓞 A).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (ringEquiv 𝓞 A)

instance ringHomInvPair₂ : RingHomInvPair (ringEquiv 𝓞 A).symm.toRingHom (ringEquiv 𝓞 A).toRingHom :=
  RingHomInvPair.of_ringEquiv (ringEquiv 𝓞 A).symm

instance (I : Ideal A) [Nontrivial (A ⧸ I)] : IsResidueAlgebra 𝓞 (A ⧸ I) where
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
    sorry -- TODO(jlcontreras): finish this

end IsResidueAlgebra

end Deformation
