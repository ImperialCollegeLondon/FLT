/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Group actions on quotients and equivariant homs
-/

@[expose] public section

@[simp]
lemma MulAction.orbitRel.Quotient.mk_smul {G X : Type*} [Group G] [MulAction G X] (g : G) (x : X) :
  (⟦g • x⟧ : orbitRel.Quotient G X) = ⟦x⟧ := Quotient.sound ⟨g, rfl⟩

/-- Given a representative for each orbit of `X` under `G`, and for each `x : X` a choice of `σ`
that sends `x` to the representative, we obtain a bijection between `G`-equivariant homs from `X`
and the product of `Stab(x)`-fixed points over each orbit representative `x`. -/
@[simps]
def MulAction.homEquivProdFixedPoints {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (σ : X → G) (hσ : ∀ a b, orbitRel G X a b → σ a • a = σ b • b) :
    (X →[G] Y) ≃ Π i : Set.range (fun i ↦ σ i • i), fixedPoints (stabilizer G i.1) Y where
  toFun f i := ⟨f i, fun ⟨σ, hσ⟩ ↦ by simp [← map_smul, show _ = _ from hσ]⟩
  invFun v := ⟨fun x ↦ (σ x)⁻¹ • v ⟨_, x, rfl⟩, by
    intro τ x
    rw [inv_smul_eq_iff]
    trans (v ⟨_, x, rfl⟩).1
    · congr 2 <;> simp [hσ (τ • x) x ⟨τ, rfl⟩]
    simp only [← mul_smul]
    refine ((v ⟨_, x, rfl⟩).2 ⟨_ * _, ?_⟩).symm
    simp [mul_smul, hσ (τ • x) x ⟨τ, rfl⟩]⟩
  left_inv f := by ext; simp; rfl
  right_inv v := by
    ext x
    have : σ x.1 • x.1 = x.1 := by obtain ⟨_, x, rfl⟩ := x; exact hσ _ _ ⟨σ x, rfl⟩
    refine inv_smul_eq_iff.mpr (.trans ?_ ((v x).2 ⟨_, this⟩).symm)
    congr 2 <;> simp [this]

/-- Given a representative for each orbit of `X` under `G`, and for each `x : X` a choice of `σ`
that sends `x` to the representative, we obtain a bijection between `X` and `∐ G/stab(x)` where
the disjoint union runs through the representatives. -/
@[simps]
def MulAction.sigmaRangeQuotientStabilizer
    {G X : Type*} [Group G] [MulAction G X]
    (σ : X → G) (hσ : ∀ a b, orbitRel G X a b → σ a • a = σ b • b) :
    (Σ i : Set.range (fun i ↦ σ i • i), G ⧸ stabilizer G i.1) ≃ X :=
  letI Y := Σ i : Set.range (fun i ↦ σ i • i), G ⧸ stabilizer G i.1
  letI f : Y → X := fun x ↦ ofQuotientStabilizer _ _ x.2
  letI g : X → Y := fun x ↦ ⟨⟨_, x, rfl⟩, ↑((σ x)⁻¹)⟩
  haveI hf : f.Injective := by
    intro ⟨⟨ia, xa, ha⟩, fa⟩ ⟨⟨ib, xb, hb⟩, fb⟩ e
    obtain ⟨fa, rfl⟩ := QuotientGroup.mk_surjective fa
    obtain ⟨fb, rfl⟩ := QuotientGroup.mk_surjective fb
    have : orbitRel G X xa xb := by
      trans fa • ia
      · symm; exact ⟨fa * σ xa, by rw [← ha, ← mul_smul]⟩
      · rw [show fa • ia = fb • ib from e]; exact ⟨fb * σ xb, by rw [← hb, ← mul_smul]⟩
    obtain rfl : ia = ib := (ha.symm.trans (hσ xa xb this)).trans hb
    congr 1
    simpa [QuotientGroup.eq, mul_smul, inv_smul_eq_iff] using! e.symm
  haveI hfg : Function.RightInverse g f := fun x ↦ inv_smul_smul (σ x) x
  ⟨f, g, fun x ↦ hf (hfg (f x)), hfg⟩
