module

public import FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.CupProduct
public import FLT.Mathlib.RepresentationTheory.Smooth.Basic

@[expose] public section

universe u

variable (K M : Type u) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [TopologicalSpace M] [AddCommGroup M] [DiscreteTopology M]
  [Finite M] (ρ : ContRepresentation ℤ (Field.absoluteGaloisGroup K) M)
  [hρ : Representation.Smooth.IsSmooth ρ.toRepresentation]

open TopRep

instance : TopologicalSpace (Additive (AlgebraicClosure K)ˣ) := ⊥

instance : DiscreteTopology (Additive (AlgebraicClosure K)ˣ) := ⟨rfl⟩

-- def ContRepresentation.ofMulDistribMulAction (M G : Type*) [Monoid M] [Topo] [CommGroup G]
--   [IsTopologicalGroup G] [MulDistribMulAction M G] :
--   ContRepresentation ℤ M (Additive G) := sorry
open Additive

noncomputable def ContRepresentation.multiplicative :
    ContRepresentation ℤ (Field.absoluteGaloisGroup K) (Additive (AlgebraicClosure K)ˣ) where
  toMonoidHom.toFun g := {
    toFun x := ofMul (g • toMul x)
    map_add' := by simp
    map_smul' := by simp
    cont := by tauto
  }
  toMonoidHom.map_one' := rfl
  toMonoidHom.map_mul' x y := by ext; simp

noncomputable abbrev LocalGaloisRep.dual : TopRep ℤ (Field.absoluteGaloisGroup K) :=
  iHom (.of ρ) (.of (ContRepresentation.multiplicative K))

open ContinuousLinearMap.CompactOpen ContRepresentation in
noncomputable def pair₀ : ρ →ⁱL ContRepresentation.linHom (LocalGaloisRep.dual K M ρ).ρ
    (ContRepresentation.multiplicative K) := {
  toFun := evalCLM
  map_add' m m' := by ext φ; simp
  map_smul' c m := by ext φ; simp
  cont := continuous_of_discreteTopology
  isIntertwining' g := by
    ext m φ
    have h1 : ∀ x, ContRepresentation.multiplicative K g
        (ContRepresentation.multiplicative K g⁻¹ x) = x := fun x ↦ by
      rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
    simp [h1] }

open ContinuousLinearMap.CompactOpen in
noncomputable def pairing (i j : ℕ) (hij : 2 = i + j) :
    continuousCohomology i (.of ρ) ⟶ TopModuleCat.linHom (k := ℤ)
      (continuousCohomology j (LocalGaloisRep.dual K M ρ)) (continuousCohomology 2
      (.of (ContRepresentation.multiplicative K))) :=
  ContinuousCohomology.cup _ _ _ (pair₀ K M ρ)
    (ContRepresentation.continuous_pair_of_discrete (pair₀ K M ρ)) i j 2 hij

lemma pairing_isPerfect1 (i j : ℕ) (hij : 2 = i + j) :
    ∀ x : continuousCohomology i (.of ρ), x ≠ 0 →
      ∃ y : continuousCohomology j (LocalGaloisRep.dual K M ρ),
      pairing K M ρ i j hij x y ≠ 0 := by
  sorry

lemma pairing_isPerfect2 (i j : ℕ) (hij : 2 = i + j) :
    ∀ y : continuousCohomology j (LocalGaloisRep.dual K M ρ), y ≠ 0 →
      ∃ x : continuousCohomology i (.of ρ),
      pairing K M ρ i j hij x y ≠ 0 := by
  sorry
