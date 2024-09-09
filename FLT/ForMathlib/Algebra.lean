import Mathlib.RingTheory.OreLocalization.Ring

-- extend localization theory to algebras

/-!

# Algebra instances of Ore Localizations

If `R` is a commutative ring with submonoid `S`, and if `A` is a commutative `R`-algebra,
then my guess is that `A[S⁻¹]` is an `R[S⁻¹]`-algebra. Let's see if I'm right and if so,
in what generality.

-/

namespace OreLocalization

variable {R A : Type*} [CommMonoid R] [CommMagma A] [MulAction R A] [IsScalarTower R A A]
  {S : Submonoid R}

@[to_additive]
private def mul' (a₁ : A) (s₁ : S) (a₂ : A) (s₂ : S) : A[S⁻¹] :=
  a₁ * a₂ /ₒ (s₂ * s₁)

@[to_additive]
private def mul''
  (a : A) (s : S) : A[S⁻¹] → A[S⁻¹] :=
  liftExpand (mul' a s) fun a₁ r₁ ⟨s₁, hs₁⟩ hr₁s₁ => by
  unfold OreLocalization.mul'
  simp only at hr₁s₁ ⊢
  rw [oreDiv_eq_iff]
  use ⟨s₁, hs₁⟩, r₁ * s₁
  simp only [Submonoid.mk_smul, Submonoid.coe_mul]
  constructor
  · rw [← smul_mul_assoc]
    rw [← smul_mul_assoc]
    rw [mul_comm]
    rw [smul_mul_assoc, smul_mul_assoc]
    rw [mul_comm]
    -- it's like a bloody Rubik's cube
    rw [smul_mul_assoc]
    rw [← mul_smul]
  · obtain ⟨s₂, hs₂⟩ := s
    simpa only [Submonoid.mk_smul, Submonoid.coe_mul] using mul_left_comm s₁ (r₁ * s₁) s₂

@[to_additive]
protected def mul : A[S⁻¹] → A[S⁻¹] → A[S⁻¹] :=
  liftExpand mul'' fun a₁ r₁ s hs => by
  obtain ⟨s₁, hs₁⟩ := s
  simp only at hs
  unfold OreLocalization.mul''
  simp
  unfold OreLocalization.mul'
  dsimp
  ext sa
  induction sa
  rename_i a s_temp
  obtain ⟨s, hs⟩ := s_temp
  rw [liftExpand_of]
  rw [liftExpand_of]
  rw [oreDiv_eq_iff]
  simp only [Submonoid.mk_smul, Submonoid.coe_mul]
  use ⟨s₁, hs₁⟩, r₁ * s₁
  simp only [Submonoid.mk_smul, Submonoid.coe_mul]
  constructor
  · rw [smul_mul_assoc]
    rw [← mul_smul]
    rw [mul_comm]
  · repeat rw [mul_assoc]
    repeat rw [mul_left_comm s₁]
    rw [mul_left_comm s]

instance : Mul (A[S⁻¹]) where
  mul := OreLocalization.mul

unseal OreLocalization.smul in
example (as bt : R[S⁻¹]) : as * bt = as • bt := rfl
 -- fails on mathlib master;
-- works if irreducibiliy of OreLocalization.smul is removed

-- Next job: make API so I can prove `Algebra (R[S⁻¹]) A[S⁻¹]`
-- Might also want `numeratorAlgHom : A →ₐ[R] A[S⁻¹]`
-- Might also want some universal property a la
/-
variable {T : Type*} [Semiring T]
variable (f : R →+* T) (fS : S →* Units T)
variable (hf : ∀ s : S, f s = fS s)

/-- The universal lift from a ring homomorphism `f : R →+* T`, which maps elements in `S` to
units of `T`, to a ring homomorphism `R[S⁻¹] →+* T`. This extends the construction on
monoids. -/
def universalHom : R[S⁻¹] →+* T :=
-/
end OreLocalization
