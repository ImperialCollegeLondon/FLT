import Mathlib.RingTheory.OreLocalization.Ring
#exit

-- extend localization theory to algebras
-- I should only be doing this in the commutative case

/-!

# Algebra instances of Ore Localizations

If `R` is a commutative ring with submonoid `S`, and if `A` is a commutative `R`-algebra,
then my guess is that `A[S⁻¹]` is an `R[S⁻¹]`-algebra. Let's see if I'm right and if so,
in what generality.

-/

namespace OreLocalization

section CommMagma

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

protected def mul_def (a : A) (s : { x // x ∈ S }) (b : A) (t : { x // x ∈ S }) :
  a /ₒ s * (b /ₒ t) = a * b /ₒ (t * s) := rfl

unseal OreLocalization.smul in
example (as bt : R[S⁻¹]) : as * bt = as • bt := rfl

end CommMagma

section One

variable {R A : Type*} [CommMonoid R] [MulAction R A] [One A] --[MulAction R A] [IsScalarTower R A A]
  {S : Submonoid R}

instance : One (A[S⁻¹]) where
  one := 1 /ₒ 1

protected lemma one_def' : (1 : A[S⁻¹]) = 1 /ₒ 1 := rfl

end One

section CommMonoid

variable {R A : Type*} [CommMonoid R] [CommMonoid A] [MulAction R A] [IsScalarTower R A A]
  {S : Submonoid R}

instance commMonoid : CommMonoid (A[S⁻¹]) where
  mul_assoc a b c := by
    induction' a with a
    induction' b with b
    induction' c with c
    change (a * b * c) /ₒ _ = (a * (b * c)) /ₒ _
    simp [mul_assoc]
  one_mul a := by
    induction' a with a
    change (1 * a) /ₒ _ = a /ₒ _
    simp
  mul_one a := by
    induction' a with a s
    simp [OreLocalization.mul_def, OreLocalization.one_def']
  mul_comm a b := by
    induction' a with a
    induction' b with b
    simp only [OreLocalization.mul_def, mul_comm]

end CommMonoid

section CommSemiring

variable {R A : Type*} [CommMonoid R] [CommRing A] [DistribMulAction R A] [IsScalarTower R A A]
  {S : Submonoid R}

lemma left_distrib' (a b c : A[S⁻¹]) :
    a * (b + c) = a * b + a * c := by
  induction' a with a s
  induction' b with b t
  induction' c with c u
  rcases oreDivAddChar' b c t u with ⟨r₁, s₁, h₁, q⟩; rw [q]; clear q
  simp only [OreLocalization.mul_def]
  rcases oreDivAddChar' (a * b) (a * c) (t * s) (u * s) with ⟨r₂, s₂, h₂, q⟩; rw [q]; clear q
  rw [oreDiv_eq_iff]
  change ∃ w, _
  use s₁ * t * s, s₂ * t * s
  simp [mul_add]
  constructor
  · congr 1
    · simp [Submonoid.smul_def, ← mul_assoc]
      simp [← mul_smul]
      have : a * (s₁ : R) • b = (s₁ : R) • (a * b) := by
        rw [mul_comm, smul_mul_assoc, mul_comm]
      rw [this]
      simp [← mul_smul]
      congr 1
      simp [mul_assoc, mul_comm, mul_left_comm]
    calc (s₁ * t * s) • r₂ • (a * c)
      _ = (s₁ * t * s : R) • r₂ • (a * c) := by rw [@Submonoid.smul_def]; simp
      _ = (r₁ * u * s : R) • r₂ • (a * c) := by rw [h₁]
      _ = (r₂ * u * s : R) • r₁ • (a * c) := ?_
      _ = (r₂ * ↑(u * s) : R) • r₁ • (a * c) := by simp [Submonoid.smul_def, mul_assoc]
      _ = (s₂ * ↑(t * s) : R) • r₁ • (a * c) := by rw [h₂]
      _ = (s₂ * t * s : R) • r₁ • (a * c) := by simp [mul_assoc]
      _ = (s₂ * t * s : R) • (a * r₁ • c) := ?_
    · simp [← mul_smul]
      congr 1
      simp [mul_assoc, mul_comm, mul_left_comm]
    · simp [← mul_smul]
      have : a * (r₁ : R) • c = (r₁ : R) • (a * c) := by
        rw [mul_comm, smul_mul_assoc, mul_comm]
      rw [this]
      simp [← mul_smul]
  · simp [mul_assoc, mul_comm, mul_left_comm]

instance : CommSemiring A[S⁻¹] where
  __ := commMonoid
  left_distrib := left_distrib'
  right_distrib a b c := by
    rw [mul_comm, mul_comm a, mul_comm b, left_distrib']
  zero_mul a := by
    induction' a with a s
    rw [OreLocalization.zero_def, OreLocalization.mul_def]
    simp
  mul_zero a := by
    induction' a with a s
    rw [OreLocalization.zero_def, OreLocalization.mul_def]
    simp

end CommSemiring


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


section first_goal

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {S : Submonoid R}

abbrev SR := R[S⁻¹]
abbrev SA := A[S⁻¹]


--unseal OreLocalization.smul in
--instance : Algebra (R[S⁻¹]) (A[S⁻¹]) where
/-
error:
failed to synthesize
  Semiring (OreLocalization S A)
-/

end first_goal

end OreLocalization
