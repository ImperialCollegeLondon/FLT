import Mathlib
import FLT.Basic.Reductions
namespace FLT
namespace FreyPackage
open Field
open LinearMap Module
open scoped TensorProduct
-- variable (p : ℕ) [Fact (Nat.Prime p)]

theorem one {K : Type*} [Field K] (a b : K) (n : ℕ) (hn : n > 2) :
  ∀ a b c : ℤ , a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n := sorry

/-- n=3 was handled by Euler, we have a proof in FLT -/
theorem FLTthree : ∀ a b c : ℕ , a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 3 + b ^ 3 ≠ c ^ 3 :=
fermatLastTheoremThree

/-- n=4 was handled by Fermat, we also have a proof in FLT -/
theorem FLTfour : ∀ a b c : ℕ , a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 4 :=
fermatLastTheoremFour

/-- we hence only need to care about n=ℓ an odd prime larger than 3,
 we can assume we have a Frey's package in this case -/
lemma reduce {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {p : ℕ} (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) : Nonempty FLT.FreyPackage :=
    FLT.FreyPackage.of_not_FermatLastTheorem_p_ge_5 ha hb hc pp hp5 H

def IsBadReduction (C : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] :Prop:= sorry

variable (p : ℕ) [Fact (Nat.Prime p)]

lemma badreduction (P : FreyPackage) :
IsBadReduction (FreyCurve P) p ↔ ((p : Int) ∣ (P.a * P.b * P.c)):= sorry

local notation "G_K" => absoluteGaloisGroup
local notation "ℤ[G]" => MonoidAlgebra ℤ

abbrev E_pclosure (C : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] : Type :=
  (C.map (algebraMap ℚ (AlgebraicClosure ℚ_[p])) ).toAffine.Point

noncomputable instance CommGroupstructure (C : WeierstrassCurve ℚ) :
 AddCommGroup (E_pclosure C p):= by classical infer_instance

def ρ_curve (C : WeierstrassCurve ℚ) : Representation ℤ (G_K ℚ_[p]) (E_pclosure C p) := sorry

/-noncomputable instance Modulestructue (C : WeierstrassCurve ℚ) :
Module (ℤ[G] (G_K ℚ_[p])) (E_pclosure C p) := sorry-/

abbrev G (q : IsLocalRing.maximalIdeal ℤ_[p]) (hq : (q : ℚ_[p]) ≠ 0) :
 Type := Additive (ℚ_[p]ˣ⧸(Subgroup.closure ({Units.mk0 (q: ℚ_[p]) hq})))

noncomputable instance AddCommMonoid
(q : IsLocalRing.maximalIdeal ℤ_[p]) (hq : (q : ℚ_[p]) ≠ 0) : AddCommMonoid (G p q hq)
:= by infer_instance

def ρ_G (q : IsLocalRing.maximalIdeal ℤ_[p]) (hq : (q : ℚ_[p]) ≠ 0) :
 Representation ℤ (G_K ℚ_[p]) (G p q hq) := sorry

/-noncomputable instance Modulestructue1
(q : IsLocalRing.maximalIdeal ℤ_[p]) (hq : (q : ℚ_[p]) ≠ 0) :
Module (ℤ[G] (G_K ℚ_[p])) (G p q hq) := sorry-/

variable {G M : Type*} [Group G] [AddCommGroup M]

structure Representation.Equiv {R : Type*} [CommSemiring R] {G : Type*} [Group G]
    {M₁ M₂ : Type*} [_root_.AddCommMonoid M₁] [_root_.AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    (ρ₁ : Representation R G M₁) (ρ₂ : Representation R G M₂)
     extends M₁ ≃ₗ[R] M₂ where
     exchange : ∀(g : G), ∀(m : M₁), toFun (ρ₁ g m) = (ρ₂ g (toFun m))

def twist (ρ : Representation ℤ G M) (δ : G →* ℤˣ) : Representation ℤ G M where
  toFun g := {
    toFun m := δ g • ρ g m
    map_add' := by aesop
    map_smul' := by {
    intro m x
    simp only [map_smul, eq_intCast, Int.cast_eq]
    exact smul_comm (δ g) m ((ρ g) x)
    }}
  map_one' := by aesop
  map_mul' g h := by {
    ext m
    simp only [map_mul, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, map_zsmul_unit]
    rw[mul_comm, mul_smul]
  }

/-This theorem can be even strengthen as topological module isomorphism, I'll write later-/
/-what's the difference between a Z tensor and a Z[G] tensor?-/
theorem Tate (P : FreyPackage) : IsBadReduction (FreyCurve P) p
→ ∃ (δ : (G_K ℚ_[p]) →* ℤˣ) , ∃ (q : IsLocalRing.maximalIdeal ℤ_[p])
(hq : (q : ℚ_[p]) ≠ 0), Nonempty (Representation.Equiv (ρ_curve p (FreyCurve P))
(twist (ρ_G p q hq) δ)) := sorry

variable (q : IsLocalRing.maximalIdeal ℤ_[p]) (hq : (q : ℚ_[p]) ≠ 0) {P : FreyPackage}
(hPp : IsBadReduction (FreyCurve P) p) (δ : (G_K ℚ_[p]) →* ℤˣ)
(hqδ : Nonempty (Representation.Equiv (ρ_curve p (FreyCurve P))
(twist (ρ_G p q hq) δ)))

section
include q hq P hPp δ hqδ
lemma q_equation : ∃(C : ℕ → ℚ_[p]), (FreyCurve P).j=
(q : ℚ_[p])⁻¹ + 744 + ∑' n : ℕ+, (C n) * q^(n:ℕ) := sorry

lemma p_valuation : Padic.valuation ((FreyCurve P).j : ℚ_[p])
 = Padic.valuation (q : ℚ_[p])⁻¹ := sorry

lemma p_valuation_mod (hp : Odd p) :
((Padic.valuation (p := p ) (q:ℤ_[p])) : ZMod (2*P.p)) = 0 := sorry

lemma p_valuation_mod2 : ((Padic.valuation (p := p ) (q:ℤ_[p])) : ZMod 2) = -8 := sorry

end

#check instIsEllipticRatFreyCurve

def rank2_p_torsion (C : WeierstrassCurve ℚ) (hC : C.IsElliptic) :
 (C.n_torsion p ≃ₗ[ZMod p] (Fin 2 → ZMod p)) := sorry

/-I believe this gonna be an easy sorry, base on rank2_p_torsion and
WeierstrassCurve.torsionGaloisRepresentation-/
abbrev r (E : WeierstrassCurve ℚ) : G_K ℚ →* (Fin 2 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p):=sorry


#check Fintype
#check ZMod
#check WeierstrassCurve.torsionGaloisRepresentation
#check Representation

end FreyPackage
end FLT
