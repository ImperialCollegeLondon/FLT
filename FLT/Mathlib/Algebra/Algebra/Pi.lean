/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import FLT.Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Pi

Material destined for Mathlib.
-/

@[expose] public section

/-- A family of semialgebra homomorphisms `g i : A →ₛₐ[φ] f i` defines a single
semialgebra homomorphism `A →ₛₐ[φ] (i : I) → f i` to the product algebra. -/
def Pi.semialgHom {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) :
    A →ₛₐ[φ] (i : I) → f i where
  __ := RingHom.pi fun i ↦ (g i).toRingHom
  map_smul' r a := by ext; simp

@[simp]
theorem Pi.semialgHom_apply {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R]
    [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) (a : A) (i : I) :
    (Pi.semialgHom _ φ g) a i = g i a :=
  rfl

/-- Given a reindexing `r : I → J` and a family of semialgebra homs
`p i : g (r i) →ₛₐ[φ] f i`, build a semialgebra hom from the product over `J` of the `g j` to
the product over `I` of the `f i`. -/
def Pi.semialgHomPi {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i) :
    ((j : J) → g j) →ₛₐ[φ] (i : I) → f i where
  toFun x w := p w (x (r w))
  map_one' := by simp [Pi.one_def]
  map_mul' x y := funext fun w => by simp [map_mul]
  map_zero' := by simp [Pi.zero_def]
  map_add' x y := funext fun w => by simp [map_add]
  map_smul' k x := funext fun w => (p w).map_smul' k (x (r w))

@[simp]
theorem Pi.semialgHomPi_apply {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i)
    (a : (j : J) → g j) (i : I) :
    Pi.semialgHomPi _ _ p a i = p i (a (r i)) := rfl

/-- Let `f : α → β` be a function on index types. A family of `R`-algebra equivalences, indexed by
`b : β`, between the product over the fiber of `b` under `f` given as
`∀ (σ : { a : α // f a = b }) → γ₁ σ.1) ≃ₐ[R] γ₂ b` lifts to an equivalence over the products
`∀ a, γ₁ a ≃ₐ[R] ∀ b, γ₂ b`. This is `Equiv.piCongrFiberwise` as an `AlgEquiv`. -/
def AlgEquiv.piCongrFiberwise {α : Type*} {β : Type*} {R : Type*} {γ₁ : α → Type*} {γ₂ : β → Type*}
    {f : α → β} [CommSemiring R] [(a : α) → Semiring (γ₁ a)] [(b : β) → Semiring (γ₂ b)]
    [(a : α) → Algebra R (γ₁ a)] [(b : β) → Algebra R (γ₂ b)]
    (e : (b : β) → ((x : { x : α // f x = b }) → γ₁ x.1) ≃ₐ[R] γ₂ b) :
    ((a : α) → γ₁ a) ≃ₐ[R] ((b : β) → γ₂ b) where
  __ := Equiv.piCongrFiberwise fun _ => (e _).toEquiv
  map_add' _ _ := by funext b; simp [← Pi.add_def]
  map_mul' _ _ := by funext b; simp [← Pi.mul_def]
  commutes' r := by funext b; simp [← (e b).commutes' r, Pi.algebraMap_def]

lemma RingHom.exists_map_single_ne_zero
    {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [Nontrivial S] (f : (Π i, R i) →+* S) :
    ∃ i, f (Pi.single i 1) ≠ 0 := by
  cases nonempty_fintype ι
  by_contra! H
  simpa [H] using DFunLike.congr_arg f (Finset.univ_sum_single 1)

/-- Given a map from a product of rings to a nontrivial ring, this is an arbitrary index whose
corresponding component is not sent to zero. -/
noncomputable
def RingHom.piIndex {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [Nontrivial S] (f : (Π i, R i) →+* S) : ι :=
  f.exists_map_single_ne_zero.choose

lemma RingHom.single_piIndex_ne_zero {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [Nontrivial S] (f : (Π i, R i) →+* S) :
    f (Pi.single f.piIndex 1) ≠ 0 :=
  f.exists_map_single_ne_zero.choose_spec

@[simp]
lemma RingHom.single_piIndex_one {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [IsDomain S] (f : (Π i, R i) →+* S) :
    f (Pi.single f.piIndex 1) = 1 :=
  mul_left_injective₀ f.single_piIndex_ne_zero (by simp [← map_mul, ← Pi.single_mul])

@[simp]
lemma RingHom.single_piIndex {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [IsDomain S] (f : (Π i, R i) →+* S) (x : Π i, R i) :
    f (Pi.single f.piIndex (x _)) = f x := by
  conv_rhs => rw [← one_mul (f x), ← f.single_piIndex_one, ← f.map_mul]
  rw [← Pi.single_mul_left, one_mul]

/-- `Pi.single` as a `NonUnitalRingHom`. -/
noncomputable
def NonUnitalRingHom.single {ι : Type*} (R : ι → Type*) [DecidableEq ι]
    [∀ i, NonUnitalNonAssocSemiring (R i)] (i) : R i →ₙ+* Π i, R i where
  __ := AddMonoidHom.single R i
  map_mul' _ _ := Pi.single_mul _ _ _

@[simp]
lemma NonUnitalRingHom.single_apply {ι : Type*} {R : ι → Type*} [DecidableEq ι]
    [∀ i, NonUnitalNonAssocSemiring (R i)] (i : ι) (x : R i) : single R i x = Pi.single i x := rfl

@[simp]
lemma RingHom.toNonUnitalRingHom_apply {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) (x : R) : f.toNonUnitalRingHom x = f x := rfl

/-- A map from a product of rings to a domain must factor through one of the components.
This is the factor map. -/
@[simps!]
noncomputable
def RingHom.projPiIndex {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [IsDomain S] (f : (Π i, R i) →+* S) :
    R f.piIndex →+* S where
  __ := f.toNonUnitalRingHom.comp (NonUnitalRingHom.single R f.piIndex)
  map_one' := by simp

/-- `Hom(∏ Rᵢ, S) ≃ ∐ Hom(Rᵢ, S)` when `S` is a domain. -/
@[simps! apply_fst apply_snd symm_apply_apply]
noncomputable
def Pi.ringHomEquivOfIsDomain {ι S : Type*} {R : ι → Type*} [Finite ι] [DecidableEq ι]
    [∀ i, Ring (R i)] [Ring S] [IsDomain S] :
    ((Π i, R i) →+* S) ≃ Σ i, R i →+* S where
  toFun f := ⟨f.piIndex, f.projPiIndex⟩
  invFun f := f.2.comp (Pi.evalRingHom R f.1)
  left_inv f := by ext; simp
  right_inv f := by
    have : Function.Injective (fun f : Σ i, R i →+* S ↦ f.2.comp (Pi.evalRingHom R f.1)) := by
      intro ⟨i₁, f₁⟩ ⟨i₂, f₂⟩ e
      obtain rfl : i₁ = i₂ := by
        by_contra H; simpa [H] using DFunLike.congr_fun e (Pi.single i₁ 1)
      congr 1
      ext x
      simpa using DFunLike.congr_fun e (Pi.single i₁ x)
    exact this (by ext; simp)

/-- `Hom(∏ Rᵢ, S) ≃ ∐ Hom(Rᵢ, S)` when `S` is a domain.
This is the `AlgHom` version of `Pi.ringHomEquivOfIsDomain`. -/
@[simps! apply_fst symm_apply_apply, simps! -isSimp apply_snd_apply]
noncomputable
def Pi.algHomEquivOfIsDomain {ι R₀ S : Type*} {R : ι → Type*} [Finite ι] [DecidableEq ι]
    [CommSemiring R₀]
    [∀ i, Ring (R i)] [∀ i, Algebra R₀ (R i)] [Ring S] [Algebra R₀ S] [IsDomain S] :
    ((Π i, R i) →ₐ[R₀] S) ≃ Σ i, (R i →ₐ[R₀] S) where
  toFun f := ⟨_, f.projPiIndex, fun r ↦ (f.single_piIndex _).trans (f.commutes r)⟩
  invFun f := f.2.comp (Pi.evalAlgHom R₀ R f.1)
  left_inv f := by
    ext x
    simp only [AlgHom.coe_comp, Function.comp_apply, Pi.evalAlgHom_apply]
    exact f.single_piIndex x
  right_inv f := by
    let emb : (Σ i, (R i →ₐ[R₀] S)) → (Σ i, (R i →+* S)) := Sigma.map id fun _ ↦ AlgHom.toRingHom
    have : emb.Injective := Function.Injective.sigma_map (fun _ _ e ↦ e)
        fun _ a b e ↦ AlgHom.ext (DFunLike.congr_fun e :)
    apply this
    exact Pi.ringHomEquivOfIsDomain.apply_symm_apply ⟨f.1, f.2.toRingHom⟩
