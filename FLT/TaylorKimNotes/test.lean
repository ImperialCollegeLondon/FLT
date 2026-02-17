import Mathlib
open Field
open scoped TensorProduct

local notation "ℤ[G]" => MonoidAlgebra ℤ
local notation "G_K" => absoluteGaloisGroup
variable (ℓ : ℕ) [Fact (Nat.Prime ℓ)]

structure FreyPackage where
  a : ℤ
  b : ℤ
  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0
  p : ℕ
  pp : Nat.Prime p
  hp5 : 5 ≤ p
  hFLT : a ^ p + b ^ p = c ^ p
  hgcdab : gcd a b = 1 -- same as saying a,b,c pairwise coprime
  ha4 : (a : ZMod 4) = 3
  hb2 : (b : ZMod 2) = 0

namespace FreyPackage

def IsBadReduction (C : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] :Prop:= sorry
def FreyCurveSimple (P : FreyPackage) : WeierstrassCurve ℚ := sorry

abbrev E_pclosure (C : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] : Type :=
  (C.map (algebraMap ℚ (AlgebraicClosure ℚ_[p])) ).toAffine.Point

noncomputable instance CommGroupstructure (C : WeierstrassCurve ℚ) :
 AddCommGroup (E_pclosure C ℓ):= by classical infer_instance

noncomputable instance Modulestructue (C : WeierstrassCurve ℚ) :
Module (ℤ[G] (G_K ℚ_[ℓ])) (E_pclosure C ℓ) := sorry

abbrev G (q : IsLocalRing.maximalIdeal ℤ_[ℓ]) (hq : (q : ℚ_[ℓ]) ≠ 0) :
 Type := Additive (ℚ_[ℓ]ˣ⧸(Subgroup.closure ({Units.mk0 (q: ℚ_[ℓ]) hq})))

noncomputable instance AddCommMonoid
(q : IsLocalRing.maximalIdeal ℤ_[ℓ]) (hq : (q : ℚ_[ℓ]) ≠ 0) : AddCommMonoid (G ℓ q hq)
:= by infer_instance

noncomputable instance Modulestructue1
(q : IsLocalRing.maximalIdeal ℤ_[ℓ]) (hq : (q : ℚ_[ℓ]) ≠ 0) :
Module (ℤ[G] (G_K ℚ_[ℓ])) (G ℓ q hq) := sorry

open scoped TensorProduct

-- Setup
variable (R : Type*) [Semiring R]
variable (M N : Type*)
  [AddCommGroup M] [Module R M] -- over a ring these imply a ℤ-module structure
  [AddCommGroup N] [Module R N]

/- Over ℤ, the tensor is available because M, N are ℤ-modules (from AddCommGroup).
   Lean provides an R-action on M ⊗[ℤ] N by letting R act on the first factor. -/
example : Module R (M ⊗[ℤ] N) := inferInstance

-- What the action does on pure tensors (first-factor action):
example (r : R) (m : M) (n : N) :
    r • (m ⊗ₜ[ℤ] n) = (r • m) ⊗ₜ[ℤ] n := by
  exact rfl   -- this is the built-in rule

/- If you prefer R acting on the second factor, you can also get that
   (under the standard compatibility instances); the simp rule is: -/
example (r : R) (m : M) (n : N) :
    r • (m ⊗ₜ[ℤ] n) = m ⊗ₜ[ℤ] (r • n) := by
  -- depending on which instance is in scope; if not, you can define it similarly
  admit

#check Submodule.Quotient.module


variable (R : Type*) [Semiring R]

-- Lean 会自动合成：R 本身是一个 R-模
#synth Module R R
#check (inferInstance : Module R R)

-- 标量乘法就是环乘法：r • x = r * x
example (r x : R) : r • x = r * x := rfl

-- geometric series with ratio 1/2 over ℕ, valued in ℝ
noncomputable def geom : ℝ := ∑' n : ℕ, (1/2 : ℝ)^n


theorem Tate (P : FreyPackage) (p : ℕ) [Fact (Nat.Prime p)] : IsBadReduction (FreyCurveSimple P) p
→ ∃ (δ : Representation ℤ (G_K ℚ_[p]) (Additive ℤˣ)), ∃ (q : IsLocalRing.maximalIdeal ℤ_[p]) (hq : (q : ℚ_[p]) ≠ 0),
Nonempty ((E_pclosure (FreyCurveSimple P) p) ≃ₗ[ℤ[G] (G_K ℚ_[p])] ((G p q hq)⊗[ℤ[G] (G_K ℚ_[p])] δ.asModule)) := sorry
