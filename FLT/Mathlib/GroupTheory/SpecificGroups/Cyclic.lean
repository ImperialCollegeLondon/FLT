/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A group with two elements is `Multiplicative (ZMod 2)`

Material for `Mathlib.GroupTheory.SpecificGroups.Cyclic`.
-/

@[expose] public section

/-- A group `G` with exactly two elements — the identity `1` and a distinguished element `g ≠ 1`,
every element being equal to one of the two — is isomorphic to `Multiplicative (ZMod 2)`, via the
isomorphism sending `g` to `Multiplicative.ofAdd 1`. The generator `g` and the exhaustion `key` are
taken as explicit data (rather than a bare `Nat.card G = 2`) so the isomorphism is computable. -/
def mulEquivMultiplicativeZModTwo {G : Type*} [Group G] [DecidableEq G] (g : G) (hg : g ≠ 1)
    (key : ∀ x : G, x = 1 ∨ x = g) : G ≃* Multiplicative (ZMod 2) :=
  have hgg : g * g = 1 := (key (g * g)).resolve_right fun h ↦ hg (mul_eq_right.mp h)
  have keyM : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = .ofAdd 1 := by decide
  have hM1 : (.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by decide
  have hMM : (.ofAdd 1 : Multiplicative (ZMod 2)) * .ofAdd 1 = 1 := by
    decide
  { toFun x := if x = 1 then 1 else .ofAdd 1
    invFun x := if x = 1 then 1 else g
    left_inv x := by rcases key x <;> grind
    right_inv x := by rcases keyM x <;> grind
    map_mul' a b := by rcases key a <;> rcases key b <;> grind
  }

end
