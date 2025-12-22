import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Basic

open LinearMap
open scoped TensorProduct

namespace Representation

variable {R V G ι : Type*} [CommRing R] [AddCommMonoid V] [Module R V] [Module.Free R V]
  [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]

variable (ρ : Representation R G V) (𝓑 : Module.Basis ι R V)

omit [Module.Free R V] [Module.Finite R V] in
@[simp]
lemma comp_def (g h : G) : ρ g ∘ₗ ρ h = ρ g * ρ h := rfl

noncomputable def gl_map_of_basis
  : G →* Matrix.GeneralLinearGroup ι R where
    toFun g := {
      val := LinearMap.toMatrix 𝓑 𝓑 (ρ g)
      inv := LinearMap.toMatrix 𝓑 𝓑 (ρ g⁻¹)
      val_inv := by rw [← toMatrix_comp, comp_def, ← map_mul]; simp
      inv_val := by rw [← toMatrix_comp, comp_def, ← map_mul]; simp
    }
    map_one' := by aesop
    map_mul' := by rintro x y; simp [LinearMap.toMatrix_mul]; norm_cast

noncomputable def baseChange (R' : Type*) [CommRing R'] [Algebra R R'] (ρ : Representation R G V)
    : Representation R' G (R' ⊗[R] V) where
  toFun g := LinearMap.baseChange R' (ρ g)
  map_one' := by aesop
  map_mul' := by aesop

scoped notation ρ "⊗ᵣ" ρ' => tprod ρ ρ'
scoped notation R' "⊗ᵣ'" ρ => baseChange R' ρ

end Representation
