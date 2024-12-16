import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Basic

open LinearMap
open scoped TensorProduct

namespace Representation

variable {R V G ι: Type*} [CommRing R] [AddCommMonoid V] [Module R V] [Module.Free R V]
  [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]

variable (ρ : Representation R G V) (𝓑 : Basis ι R V)

omit [Module.Free R V] [Module.Finite R V] in
@[simp]
lemma comp_eq_mul (g h : G): ρ g ∘ₗ ρ h = ρ (g * h) := by
  simp_all only [map_mul]
  rfl

noncomputable def GL_map_of_representation_of_basis
  : G →* Matrix.GeneralLinearGroup ι R where
    toFun g := {
      val := LinearMap.toMatrix 𝓑 𝓑 (ρ g)
      inv := LinearMap.toMatrix 𝓑 𝓑 (ρ g⁻¹)
      val_inv := by rw [← toMatrix_comp, comp_eq_mul]; simp
      inv_val := by rw [← toMatrix_comp, comp_eq_mul]; simp
    }
    map_one' := by aesop
    map_mul' := by rintro x y; simp [LinearMap.toMatrix_mul]; norm_cast

noncomputable def tprod' (R' : Type*) [CommRing R'] [Algebra R R'] (ρ : Representation R G V)
    : Representation R G (R' ⊗[R] V) where
  toFun g := TensorProduct.map .id (ρ g)
  map_one' := by simp; rw [← LinearMap.one_eq_id, TensorProduct.map_one]
  map_mul' := by aesop

scoped notation ρ "⊗ᵣ" ρ' => tprod ρ ρ'
scoped notation R' "⊗ᵣ'" ρ => tprod' R' ρ

end Representation
