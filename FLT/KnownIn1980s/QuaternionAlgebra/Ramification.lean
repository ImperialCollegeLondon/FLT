/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib

/-!
# Challenge: prescribing the ramification set of a quaternion algebra

A formalization target from John Voight, *Quaternion Algebras* (GTM 288), Proposition 27.5.15
(p. 456):

> Let `Σ ⊆ Pl F` be a finite subset of noncomplex places of `F` of even cardinality.
> Then there exists a quaternion algebra `B` over `F` with `Ram B = Σ`.

This file intentionally keeps only the vocabulary needed to state the proposition.  Infinite and
finite places are kept separate, and local ramification is defined by the Brauer class of the
base-changed Mathlib quaternion algebra over the corresponding completion.
-/

universe w u v

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField Quaternion TensorProduct

section BrauerGroupGroup

variable {k : Type u} [Field k]
variable {A B : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
  [Ring B] [Algebra k B] [FiniteDimensional k B]

lemma Module.End.finrank_eq {R M : Type*} [CommSemiring R] [StrongRankCondition R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (n : ℕ) (hn : Module.finrank R M = n) :
    Module.finrank R (Module.End R M) = n ^ 2 := by
  simp [(algEquivMatrix (Module.finBasisOfFinrankEq R M hn)).toLinearEquiv.finrank_eq,
    finrank_matrix, pow_two]

instance tensorProduct_isSimple {A B : Type*} [Ring A] [Algebra k A] [Ring B]
    [Algebra k B] [IsSimpleRing A] [Algebra.IsCentral k A] [IsSimpleRing B] :
    IsSimpleRing (A ⊗[k] B) := by
  sorry

instance tensorProduct_isSimple_of_right {A B : Type*} [Ring A] [Algebra k A]
    [Ring B] [Algebra k B] [IsSimpleRing A] [IsSimpleRing B] [Algebra.IsCentral k B] :
    IsSimpleRing (A ⊗[k] B) := by
  sorry

instance tensorProduct_isCentral {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    [Algebra.IsCentral k A] [Algebra.IsCentral k B] :
    Algebra.IsCentral k (A ⊗[k] B) := by
  sorry

instance Algebra.IsCentral.baseChange {A : Type*} [Ring A] [Algebra k A] (L : Type*)
    [Field L] [Algebra k L] [Algebra.IsCentral k A] :
    Algebra.IsCentral L (L ⊗[k] A) := by
  sorry

lemma mulLeftRight_bijective_of_simple (n : ℕ) [IsSimpleRing A] [Algebra.IsCentral k A]
    (hn : Module.finrank k A = n) :
    Function.Bijective (AlgHom.mulLeftRight k A) := by
  let e := algEquivMatrix (Module.finBasisOfFinrankEq k A hn)
  refine ⟨RingHom.injective _, LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.mulLeftRight k A).toLinearMap) ?_ |>.1 <| RingHom.injective _⟩
  simp [Module.End.finrank_eq, MulOpposite.finrank, pow_two]

/-- A central simple algebra tensored with its opposite algebra is a matrix algebra. -/
noncomputable def centralSimpleTensorOp (n : ℕ) [IsSimpleRing A] [Algebra.IsCentral k A]
    (hn : Module.finrank k A = n) : A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
  (AlgEquiv.ofBijective _ (mulLeftRight_bijective_of_simple n hn)).trans <|
    algEquivMatrix (Module.finBasisOfFinrankEq k A hn)

/-- The opposite algebra tensored with a central simple algebra is a matrix algebra. -/
noncomputable def opTensorCentralSimple (n : ℕ) [IsSimpleRing A] [Algebra.IsCentral k A]
    (hn : Module.finrank k A = n) : Aᵐᵒᵖ ⊗[k] A ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
  (Algebra.TensorProduct.comm k Aᵐᵒᵖ A).trans <| centralSimpleTensorOp n hn

namespace BrauerGroup

/-- Make a Brauer class from a finite-dimensional central simple algebra. -/
def mk (k : Type u) (A : Type*) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [IsSimpleRing A] [Algebra.IsCentral k A] : BrauerGroup k :=
  Quotient.mk _ ⟨AlgCat.of k A⟩

lemma mk_eq_mk [IsSimpleRing B] [Algebra.IsCentral k B] [IsSimpleRing A]
    [Algebra.IsCentral k A] :
    mk k A = mk k B ↔
      ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧
        Nonempty (Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B) := by
  rw [mk, mk, Quotient.eq]
  rfl

lemma mk_congr [IsSimpleRing B] [Algebra.IsCentral k B] [IsSimpleRing A]
    [Algebra.IsCentral k A] (e : A ≃ₐ[k] B) :
    mk k A = mk k B := by
  rw [mk_eq_mk]
  exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨AlgEquiv.mapMatrix e⟩⟩

instance instOneFLT : One (BrauerGroup k) :=
  ⟨mk k k⟩

lemma mk_self_eq_one : mk k k = 1 :=
  rfl

lemma mk_matrix_eq_one (n : Type) [Nonempty n] [Fintype n] [DecidableEq n] :
    mk k (Matrix n n k) = 1 := by
  rw [← mk_self_eq_one, mk_eq_mk]
  use 1, Fintype.card n, one_ne_zero, ne_of_gt Fintype.card_pos
  refine ⟨?_⟩
  have e1 := Matrix.uniqueAlgEquiv (m := Fin 1) (R := k) (A := Matrix n n k)
  refine AlgEquiv.trans ?_ <| Matrix.reindexAlgEquiv k k (Fintype.equivFin n)
  convert e1
  · with_reducible_and_instances rfl
  · with_reducible_and_instances rfl

@[elab_as_elim]
protected theorem induction (x : BrauerGroup k) (P : BrauerGroup k → Prop)
    (h : ∀ (A : Type u), [Ring A] → [Algebra k A] → [FiniteDimensional k A] →
      [IsSimpleRing A] → [Algebra.IsCentral k A] → P (mk k A)) : P x := by
  refine Quotient.inductionOn x fun C => ?_
  exact h C

variable {β : Sort w}

/-- Lift a function on central simple algebras that is invariant under Brauer equivalence to a
function out of the Brauer group. -/
def lift (f : CSA.{u, u} k → β)
    (hf : ∀ X Y : CSA.{u, u} k, IsBrauerEquivalent X Y → f X = f Y) :
    BrauerGroup k → β :=
  Quotient.lift f hf

@[simp]
lemma lift_mk (f : CSA.{u, u} k → β)
    (hf : ∀ X Y : CSA.{u, u} k, IsBrauerEquivalent X Y → f X = f Y)
    (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [Algebra.IsCentral k A] :
    lift f hf (mk k A) = f ⟨AlgCat.of k A⟩ :=
  rfl

/-- Lift a binary function on central simple algebras that is invariant under Brauer equivalence in
each argument to the Brauer group. -/
def lift₂ (f : CSA.{u, u} k → CSA.{u, u} k → β)
    (hf : ∀ X Y Z W : CSA.{u, u} k, IsBrauerEquivalent X Z →
      IsBrauerEquivalent Y W → f X Y = f Z W) :
    BrauerGroup k → BrauerGroup k → β :=
  Quotient.lift₂ f hf

@[simp]
lemma lift₂_mk (f : CSA.{u, u} k → CSA.{u, u} k → β)
    (hf : ∀ X Y Z W : CSA.{u, u} k, IsBrauerEquivalent X Z →
      IsBrauerEquivalent Y W → f X Y = f Z W)
    (A B : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [Algebra.IsCentral k A] [Ring B] [Algebra k B] [FiniteDimensional k B]
    [IsSimpleRing B] [Algebra.IsCentral k B] :
    lift₂ f hf (mk k A) (mk k B) = f ⟨AlgCat.of k A⟩ ⟨AlgCat.of k B⟩ :=
  rfl

/-- A spelling of Brauer equivalence for algebras rather than bundled `CSA`s. -/
abbrev IsBrauerEquivalent' (A B : Type u) [Ring A] [Algebra k A] [Ring B] [Algebra k B] :=
  ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧
    Nonempty (Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B)

lemma isBrauerEquivalent_tensor {A B C D : Type u}
    [Ring A] [Algebra k A] [Ring B] [Algebra k B] [Ring C] [Algebra k C]
    [Ring D] [Algebra k D] (hAC : IsBrauerEquivalent' (k := k) A C)
    (hBD : IsBrauerEquivalent' (k := k) B D) :
    IsBrauerEquivalent' (k := k) (A ⊗[k] B) (C ⊗[k] D) := by
  obtain ⟨n₁, m₁, hn₁, hm₁, ⟨e₁⟩⟩ := hAC
  obtain ⟨n₂, m₂, hn₂, hm₂, ⟨e₂⟩⟩ := hBD
  refine ⟨n₁ * n₂, m₁ * m₂, Nat.mul_ne_zero hn₁ hn₂,
    Nat.mul_ne_zero hm₁ hm₂, ⟨?_⟩⟩
  exact (Matrix.reindexAlgEquiv k _ (finProdFinEquiv (m := n₁) (n := n₂))).symm.trans <|
    (Matrix.kroneckerTMulAlgEquiv (m := Fin n₁) (n := Fin n₂) (R := k) (S := k)
      (A := A) (B := B)).symm.trans <|
    (Algebra.TensorProduct.congr e₁ e₂).trans <|
    (Matrix.kroneckerTMulAlgEquiv (m := Fin m₁) (n := Fin m₂) (R := k) (S := k)
      (A := C) (B := D)).trans <|
    Matrix.reindexAlgEquiv k _ (finProdFinEquiv (m := m₁) (n := m₂))

instance instMulFLT : Mul (BrauerGroup k) where
  mul := lift₂ (fun A => fun B => mk k (A ⊗[k] B)) fun A B C D h1 h2 => by
    rw [mk_eq_mk]
    exact isBrauerEquivalent_tensor h1 h2

lemma mk_mul_mk (A B : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSimpleRing A] [Algebra.IsCentral k A] [Ring B] [Algebra k B]
    [FiniteDimensional k B] [IsSimpleRing B] [Algebra.IsCentral k B] :
    mk k A * mk k B = mk k (A ⊗[k] B) :=
  rfl

lemma mul_one' (x : BrauerGroup k) : x * 1 = x := by
  induction x using BrauerGroup.induction with
  | h A =>
      rw [← mk_self_eq_one, mk_mul_mk]
      exact mk_congr (Algebra.TensorProduct.rid _ _ _)

lemma one_mul' (x : BrauerGroup k) : 1 * x = x := by
  induction x using BrauerGroup.induction with
  | h A =>
      rw [← mk_self_eq_one, mk_mul_mk]
      exact mk_congr (Algebra.TensorProduct.lid _ _)

lemma mul_assoc' (x y z : BrauerGroup k) : x * y * z = x * (y * z) := by
  induction x using BrauerGroup.induction with
  | h A =>
      induction y using BrauerGroup.induction with
      | h B =>
          induction z using BrauerGroup.induction with
          | h C =>
              rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk]
              exact mk_congr (Algebra.TensorProduct.assoc ..)

instance instInvFLT : Inv (BrauerGroup k) where
  inv := lift (fun A => mk k Aᵐᵒᵖ) fun A B h => by
    rw [mk_eq_mk]
    obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
    refine ⟨n, m, hn, hm, ⟨?_⟩⟩
    exact AlgEquiv.mopMatrix.trans <| e.op.trans AlgEquiv.mopMatrix.symm

lemma mk_inv (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsSimpleRing A] [Algebra.IsCentral k A] :
    (mk k A)⁻¹ = mk k Aᵐᵒᵖ :=
  rfl

lemma inv_mul_cancel' (x : BrauerGroup k) : x⁻¹ * x = 1 := by
  induction x using BrauerGroup.induction with
  | h A =>
      have : NeZero (Module.finrank k A) := ⟨ne_of_gt Module.finrank_pos⟩
      rw [mk_inv, mk_mul_mk, ← mk_matrix_eq_one (k := k) (Fin (Module.finrank k A))]
      exact mk_congr <| opTensorCentralSimple _ rfl

lemma mul_comm' (x y : BrauerGroup k) : x * y = y * x := by
  induction x using BrauerGroup.induction with
  | h A =>
      induction y using BrauerGroup.induction with
      | h B =>
          rw [mk_mul_mk, mk_mul_mk]
          exact mk_congr (Algebra.TensorProduct.comm _ _ _)

instance instCommGroupFLT : CommGroup (BrauerGroup k) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'
  mul_comm := mul_comm'

/-- Extend scalars on Brauer classes, using an invariance proof for Brauer equivalence. -/
protected def map (L : Type*) [Field L] [Algebra k L]
    (h : ∀ A B : CSA.{u, u} k, IsBrauerEquivalent A B →
      IsBrauerEquivalent (K := L) (.mk (AlgCat.of L (L ⊗[k] A)))
        (.mk (AlgCat.of L (L ⊗[k] B)))) :
    BrauerGroup k → BrauerGroup L :=
  Quotient.map _ h

lemma map_mk (L : Type*) [Field L] [Algebra k L]
    (h : ∀ A B : CSA.{u, u} k, IsBrauerEquivalent A B →
      IsBrauerEquivalent (K := L) (.mk (AlgCat.of L (L ⊗[k] A)))
        (.mk (AlgCat.of L (L ⊗[k] B))))
    (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
    [Algebra.IsCentral k A] :
    BrauerGroup.map L h (mk k A) = mk L (L ⊗[k] A) :=
  rfl

/-- Matrix algebras over an extension field as scalar extensions of matrix algebras. -/
def matrixEquivTensorL (K : Type u) (L : Type*) [Field K] [Field L] [Algebra K L]
    (n : Type*) [Fintype n] [DecidableEq n]
    (C : Type*) [Ring C] [Algebra K C] [Algebra L C] [IsScalarTower K L C] :
    Matrix n n C ≃ₐ[L] C ⊗[K] Matrix n n K :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n K C).toRingEquiv) fun l => by
    change matrixEquivTensor n K C (algebraMap L (Matrix n n C) l) =
      algebraMap L (C ⊗[K] Matrix n n K) l
    have key :
        (matrixEquivTensor n K C).symm
            (algebraMap L C l ⊗ₜ[K] (1 : Matrix n n K)) =
          algebraMap L (Matrix n n C) l := by
      rw [matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
        Algebra.algebraMap_eq_smul_one (R := L) (A := Matrix n n C) l,
        IsScalarTower.algebraMap_smul C l (1 : Matrix n n C)]
    rw [Algebra.TensorProduct.algebraMap_apply, ← key, AlgEquiv.apply_symm_apply]

/-- Base change commutes with matrix algebras. -/
def matrixBaseChange (K : Type u) (L : Type*) [Field K] [Field L] [Algebra K L]
    (n : Type*) [Fintype n] [DecidableEq n] (A : Type*) [Ring A] [Algebra K A] :
    Matrix n n (L ⊗[K] A) ≃ₐ[L] L ⊗[K] Matrix n n A :=
  (matrixEquivTensorL K L n (L ⊗[K] A)).trans <|
    (Algebra.TensorProduct.assoc K K L L A (Matrix n n K)).trans <|
      Algebra.TensorProduct.congr AlgEquiv.refl (matrixEquivTensor n K A).symm

open Algebra.TensorProduct in
/-- Scalar extension as a group homomorphism on the Brauer group. -/
def baseChange (K : Type u) (L : Type (max u v)) [Field K] [Field L] [Algebra K L] :
    BrauerGroup K →* BrauerGroup L where
  toFun := BrauerGroup.map (k := K) L fun A B h => by
    obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
    simp only [IsBrauerEquivalent]
    refine ⟨n, m, hn, hm, ⟨?_⟩⟩
    exact (matrixBaseChange K L (Fin n) A).trans <|
      (congr AlgEquiv.refl e).trans <| (matrixBaseChange K L (Fin m) B).symm
  map_one' := by
    rw [← mk_self_eq_one, ← mk_self_eq_one, map_mk]
    exact mk_congr (Algebra.TensorProduct.rid _ _ _)
  map_mul' x y := by
    induction x using BrauerGroup.induction with
    | h A =>
        induction y using BrauerGroup.induction with
        | h B =>
            rw [map_mk, map_mk, mk_mul_mk, mk_mul_mk, map_mk]
            refine mk_congr <| ((Algebra.TensorProduct.assoc K K L L A B).symm.trans
              (congr (Algebra.TensorProduct.rid L L (L ⊗[K] A)).symm AlgEquiv.refl)).trans
              (Algebra.TensorProduct.assoc K L L (L ⊗[K] A) L B)

@[simp]
lemma baseChange_mk (K : Type u) (L : Type (max u v)) [Field K] [Field L] [Algebra K L]
    (A : Type u) [Ring A] [Algebra K A] [FiniteDimensional K A] [IsSimpleRing A]
    [Algebra.IsCentral K A] :
    baseChange K L (mk K A) = mk L (L ⊗[K] A) :=
  rfl

end BrauerGroup

end BrauerGroupGroup

namespace VoightRamification

variable (F : Type u) [Field F] [NumberField F]

/-- `ℍ[E, a, 0, b]` is central over `E`.

This is the centrality prerequisite for putting the Mathlib quaternion algebra in the Brauer
group. -/
theorem quaternionAlgebra_isCentral {E : Type*} [Field E] [CharZero E]
    {a b : E} (ha : a ≠ 0) : Algebra.IsCentral E ℍ[E, a, 0, b] := by
  sorry

/-- `ℍ[E, a, 0, b]` is simple when `a` and `b` are nonzero.

This is the simplicity prerequisite for putting the Mathlib quaternion algebra in the Brauer
group. -/
theorem quaternionAlgebra_isSimple {E : Type*} [Field E] [CharZero E]
    {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) : IsSimpleRing ℍ[E, a, 0, b] := by
  sorry

/-- A finite-dimensional central simple algebra is split iff its Brauer class is trivial. -/
def IsSplit (k A : Type u) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [IsSimpleRing A] [Algebra.IsCentral k A] : Prop :=
  BrauerGroup.mk k A = 1

/-- A finite-dimensional central simple algebra is ramified iff it is not split. -/
def IsRamified (k A : Type u) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [IsSimpleRing A] [Algebra.IsCentral k A] : Prop :=
  ¬ IsSplit k A

/-- The Brauer class of the Mathlib quaternion algebra `ℍ[E, a, 0, b]`.

The only missing inputs are the centrality and simplicity facts above; once those are available,
Mathlib's `CSA` and `BrauerGroup` definitions construct the class directly. -/
noncomputable def quaternionBrauerClass (E : Type u) [Field E] [CharZero E]
    (a b : E) (ha : a ≠ 0) (hb : b ≠ 0) : BrauerGroup E :=
  letI : Algebra.IsCentral E ℍ[E, a, 0, b] := quaternionAlgebra_isCentral ha
  letI : IsSimpleRing ℍ[E, a, 0, b] := quaternionAlgebra_isSimple ha hb
  BrauerGroup.mk E ℍ[E, a, 0, b]

/-- The concrete quaternion algebra `ℍ[E, a, 0, b]` is split iff its Brauer class is trivial. -/
def IsSplitQuaternionAlgebra (E : Type u) [Field E] [CharZero E]
    (a b : E) (ha : a ≠ 0) (hb : b ≠ 0) : Prop :=
  quaternionBrauerClass E a b ha hb = 1

/-- The quaternion algebra `ℍ[K, a, 0, b]` is split after base change to `E`. -/
def IsSplitQuaternionAlgebraBaseChange (K : Type u) (E : Type (max u v)) [Field K]
    [Field E] [Algebra K E] [CharZero K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Prop :=
  BrauerGroup.baseChange K E (quaternionBrauerClass K a b ha hb) = 1

/-- `ℍ[F, a, 0, b]` is split at the infinite place `v` iff its Brauer class after base
change to the completion `F_v` is trivial. -/
def IsSplitAtInfinitePlace (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : InfinitePlace F) : Prop :=
  IsSplitQuaternionAlgebraBaseChange F v.Completion a b ha hb

/-- `ℍ[F, a, 0, b]` is ramified at the infinite place `v` iff it is not split there. -/
def IsRamifiedAtInfinitePlace (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : InfinitePlace F) : Prop :=
  ¬ IsSplitAtInfinitePlace F a b ha hb v

/-- `ℍ[F, a, 0, b]` is split at the finite place `v` iff its Brauer class after base
change to the `v`-adic completion `F_v` is trivial. -/
def IsSplitAtFinitePlace (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  IsSplitQuaternionAlgebraBaseChange F (v.adicCompletion F) a b ha hb

/-- `ℍ[F, a, 0, b]` is ramified at the finite place `v` iff it is not split there. -/
def IsRamifiedAtFinitePlace (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ¬ IsSplitAtFinitePlace F a b ha hb v

/-- The infinite-place part of `Ram ℍ[F, a, 0, b]`. -/
def ramificationSetInfinite (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Set (InfinitePlace F) :=
  {v | IsRamifiedAtInfinitePlace F a b ha hb v}

/-- The finite-place part of `Ram ℍ[F, a, 0, b]`. -/
def ramificationSetFinite (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Set (HeightOneSpectrum (𝓞 F)) :=
  {v | IsRamifiedAtFinitePlace F a b ha hb v}

/-- **Voight, *Quaternion Algebras*, Proposition 27.5.15.**

Let `Σ ⊆ Pl F` be a finite subset of noncomplex places of `F` of even cardinality.  Then there
exists a quaternion algebra `B` over `F` with `Ram B = Σ`. -/
theorem exists_quaternionAlgebra_ramificationSet_eq
    (S_infinite : Finset (InfinitePlace F))
    (S_finite : Finset (HeightOneSpectrum (𝓞 F)))
    (hnoncomplex : ∀ v ∈ S_infinite, ¬ v.IsComplex)
    (heven : Even (S_infinite.card + S_finite.card)) :
    ∃ (a b : F) (ha : a ≠ 0) (hb : b ≠ 0),
      ramificationSetInfinite F a b ha hb = (S_infinite : Set (InfinitePlace F)) ∧
      ramificationSetFinite F a b ha hb = (S_finite : Set (HeightOneSpectrum (𝓞 F))) := by
  sorry

end VoightRamification

end
