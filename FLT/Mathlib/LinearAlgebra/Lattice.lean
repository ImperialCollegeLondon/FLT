/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-

# Lattices (A-modules in K-vector spaces)

A fixed free A-module in a given K-vector space.

-/

section defs

variable (A K : Type*) [CommRing A] [Field K]
    [Algebra A K]

/-- If K is an A-algebra and V is a vector space over K, then this
is the A-lattice spanned by a basis for V given by the axiom
of choice. -/
def IntegralLattice (V : Type*) [AddCommGroup V] [Module K V]
    [Module A V] : Type _ :=
  (Submodule.span A (Module.Basis.ofVectorSpaceIndex K V) : Submodule A V)

namespace IntegralLattice

variable (V : Type*) [AddCommGroup V] [Module K V]
    [Module A V] [IsScalarTower A K V]

instance : AddCommGroup (IntegralLattice A K V) :=
  inferInstanceAs (AddCommGroup (Submodule.span _ _))

instance : Module A (IntegralLattice A K V) :=
  inferInstanceAs (Module A (Submodule.span _ _))

/-- The obvious linear map from finitely-supported A-valued functions on a K-basis
for V to the A-span of this basis. -/
def basis_repr_symm :
  ((Module.Basis.ofVectorSpaceIndex K V) →₀ A) →ₗ[A] (IntegralLattice A K V) where
    toFun f := f.sum (fun i a ↦ a • ⟨i.1, Submodule.mem_span_of_mem i.2⟩)
    map_add' f₁ f₂ := by
      rw [Finsupp.sum_add_index' (by simp)]
      intros
      exact add_smul _ _ _
    map_smul' k f := by
      rw [Finsupp.sum_smul_index, Finsupp.smul_sum]
      · simp_rw [mul_smul]
        rfl
      · simp

lemma basis_repr_symm_apply (f : (Module.Basis.ofVectorSpaceIndex K V) →₀ A) :
    ((basis_repr_symm A K V f).1 : V) =
    (Module.Basis.ofVectorSpace K V).repr.symm
      (f.mapRange (algebraMap A K) (map_zero _)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add]
    change _ + _ = _
    rw [hf, hg]
    rw [Finsupp.mapRange_add, map_add]
    exact map_add _
  | single a b =>
    simp [basis_repr_symm]
    rfl

lemma basis_repr_symm_single_apply (i : Module.Basis.ofVectorSpaceIndex K V) (a : A) :
    (basis_repr_symm A K V (Finsupp.single i a)).1 = a • i.1 := by
  simp [basis_repr_symm_apply]

omit [Algebra A K] [IsScalarTower A K V] in
lemma basis_repr_symm_surjective : Function.Surjective (basis_repr_symm A K V) := by
  intro ⟨v, hv⟩
  induction hv using Submodule.span_induction with
  | mem x h =>
    use Finsupp.single ⟨x, h⟩ 1
    simp [basis_repr_symm]
  | zero => exact ⟨0, by simp [basis_repr_symm]; rfl⟩
  | add x y hx hy a b =>
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    use a + b
    simp only [basis_repr_symm, LinearMap.coe_mk, AddHom.coe_mk] at ha hb ⊢
    rw [Finsupp.sum_add_index', ha, hb]
    · rfl
    · simp
    · simp [add_smul]
  | smul a x hx f =>
    obtain ⟨f, hf⟩ := f
    use a • f
    simp [basis_repr_symm] at hf ⊢
    simp [hf]
    rfl

-- for injectivity need A -> K injective

variable [FaithfulSMul A K]

lemma basis_repr_symm_injective :
    Function.Injective (basis_repr_symm A K V) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  suffices Finsupp.mapRange (algebraMap A K) (map_zero _) f = 0 by
    apply Finsupp.mapRange_injective (algebraMap A K) (map_zero _)
    · rw [← faithfulSMul_iff_algebraMap_injective]
      infer_instance
    · simp [this]
  have hf' : ((basis_repr_symm A K V) f).1 = 0 := by simp [hf]
  rwa [basis_repr_symm_apply, LinearEquiv.map_eq_zero_iff] at hf'

/-- The equivalence between finitely supported A-valued functions on a K-basis of V
(chosen by the axiom of choice) and the A-span of this basis. -/
noncomputable def basis_repr_symm_equiv :
    ((Module.Basis.ofVectorSpaceIndex K V) →₀ A) ≃ₗ[A] (IntegralLattice A K V) :=
  LinearEquiv.ofBijective (basis_repr_symm A K V)
    ⟨basis_repr_symm_injective A K V, basis_repr_symm_surjective A K V⟩

/-- The canonical A-basis of `IntegralLattice A K V`. Equal (mathematically)
to the K-basis of V given by the axiom of choice. -/
noncomputable def basis : Module.Basis
  (Module.Basis.ofVectorSpaceIndex K V) A (IntegralLattice A K V) where
    repr := (basis_repr_symm_equiv A K V).symm

lemma basis_index (i : (Module.Basis.ofVectorSpaceIndex K V)) :
    basis A K V i = (basis_repr_symm A K V) (Finsupp.single i 1) := by
  rfl

instance [Module.Finite K V] : Module.Finite A (IntegralLattice A K V) :=
  have := Module.Finite.finite_basis (Module.Basis.ofVectorSpace K V)
  Module.Finite.of_basis (basis A K V)

/-- The canonical inclusion from the A-span of a K-basis of V, to V. -/
def inclusion : IntegralLattice A K V →ₛₗ[algebraMap A K] V where
  toFun v := v.1
  map_add' _ _ := rfl
  map_smul' a v := (algebraMap_smul K a v.1).symm

lemma inclusion_basis (i : Module.Basis.ofVectorSpaceIndex K V) :
    inclusion A K V (basis A K V i) = Module.Basis.ofVectorSpace K V i := by
  simp [inclusion, basis_index, basis_repr_symm_single_apply]

-- for IsTensorProduct but not sure I'll need it
-- def f₁ : ((IntegralLattice A K V) →ₗ[A] K →ₗ[A] V) where
--   toFun m := .restrictScalars A (.toSpanSingleton K V m.1)
--   map_add' _ _ := by ext; exact smul_add _ _ _
--   map_smul' _ _ := by ext; exact smul_comm _ _ _

-- def f₂ : (K →ₗ[A] (IntegralLattice A K V) →ₗ[A] V) where
--   toFun k := k • (Submodule.subtype _)
--   map_add' k₁ k₂ := by ext; exact add_smul _ _ _
--   map_smul' a k := by ext; exact smul_assoc _ _ _

end IntegralLattice

-- should be elsewhere
namespace Module.Basis

open TensorProduct in
/-- If S is an R-algebra, M is an R-module and N is an S-module, both with
bases indexed by the same indexing set `ι`, then this
is the canonical S-linear map `S ⊗[R] M ≃ₗ[S] N` sending a basis element to
the basis element indexed by the same element of `ι`. -/
noncomputable def baseChangeEquiv (ι : Type*) (R S M N : Type*)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [DecidableEq ι]
    (bR : Module.Basis ι R M) (bS : Module.Basis ι S N) :
    S ⊗[R] M ≃ₗ[S] N :=
  (bR.repr.baseChange R S M _) ≪≫ₗ (finsuppScalarRight' R _ ι _) ≪≫ₗ bS.repr.symm

lemma _root_.TensorProduct.finsuppScalarRight'_symm_apply_single {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] {ι : Type*} [DecidableEq ι] (S : Type*)
    [CommSemiring S] [Algebra R S] [Module S M] [IsScalarTower R S M] (i : ι) (m : M) :
    (TensorProduct.finsuppScalarRight' R M ι S).symm (Finsupp.single i m) =
    (m ⊗ₜ[R] Finsupp.single i 1) := by
  convert TensorProduct.finsuppScalarRight_symm_apply_single i m

lemma _root_.TensorProduct.finsuppScalarRight'_apply_single {R : Type*} [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] {ι : Type*} [DecidableEq ι] {S : Type*} [CommSemiring S]
    [Algebra R S] [Module S M] [IsScalarTower R S M] (i : ι) (m : M) :
    (TensorProduct.finsuppScalarRight' R M ι S) (m ⊗ₜ[R] Finsupp.single i 1) =
    (Finsupp.single i m) := by
  apply (Equiv.apply_eq_iff_eq_symm_apply (TensorProduct.finsuppScalarRight' R M ι S).toEquiv).mpr
  exact (TensorProduct.finsuppScalarRight'_symm_apply_single S i m).symm

lemma baseChangeEquiv_apply_basis {ι R S M N : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [DecidableEq ι]
    (bR : Module.Basis ι R M) (bS : Module.Basis ι S N) (i : ι) (s : S) :
    baseChangeEquiv ι R S M N bR bS (s ⊗ₜ bR i) = s • bS i := by
  simp [baseChangeEquiv, LinearEquiv.baseChange_tmul,
    TensorProduct.finsuppScalarRight'_apply_single]

open TensorProduct in
lemma baseChangeEquiv_apply {ι R S M N : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [DecidableEq ι]
    {bR : Module.Basis ι R M} {bS : Module.Basis ι S N} (α : M →ₛₗ[algebraMap R S] N)
    (hα : ∀ i, α (bR i) = bS i) (s : S) (m : M) :
    baseChangeEquiv ι R S M N bR bS (s ⊗ₜ m) = s • α m := by
  nth_rewrite 1 2 [← bR.linearCombination_repr m]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, tmul_sum, map_sum, Finset.smul_sum,
    map_smulₛₗ, hα, smul_comm s, ← mul_smul]
  simp only [tmul_smul, smul_tmul', Algebra.smul_def, ← baseChangeEquiv_apply_basis bR bS]

-- -- should be elsewhere; also is not needed
-- open TensorProduct in
-- noncomputable def baseChangeEquiv'' (ι : Type*) (R S M N : Type*)
--     [CommRing R] [CommRing S] [Algebra R S]
--     [CommRing M] [Algebra R M] [CommRing N] [Algebra S N]
--     [DecidableEq ι]
--     (bR : Module.Basis ι R M) (bS : Module.Basis ι S N)
--     (P : Type*) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P] :
--     P ⊗[R] M ≃ₗ[S] P ⊗[S] N :=
--   AlgebraTensorModule.congr (TensorProduct.rid S P).symm (LinearEquiv.refl R M) ≪≫ₗ
--   AlgebraTensorModule.assoc _ _ _ _ _ _ ≪≫ₗ
--   AlgebraTensorModule.congr (LinearEquiv.refl S P)
--     (baseChangeEquiv ι R S M N bR bS)

lemma foo {ι R M P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (b : Module.Basis ι R M) (f g : M →ₗ[R] P) (hb : ∀ i, f (b i) = g (b i)) : f = g := by
  exact ext b hb

open TensorProduct in
/-- If S is an R-algebra, M is an R-module and N is an S-module, both with
bases indexed by the same indexing set `ι`, and if `P` is an `S`-algebra
(and hence an `R`-algebra) then this
is the canonical `P`-linear map `P ⊗[R] M ≃ₗ[P] P ⊗[S] N` sending a basis
element to the basis element indexed by the same element of `ι`. -/
noncomputable def baseChangeEquiv' (ι : Type*) (R S M N : Type*)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [DecidableEq ι]
    (bR : Module.Basis ι R M) (bS : Module.Basis ι S N)
    (P : Type*) [Ring P] [Algebra R P] [Algebra S P] [IsScalarTower R S P] :
    P ⊗[R] M ≃ₗ[P] P ⊗[S] N :=
  (AlgebraTensorModule.cancelBaseChange R S P P M).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl P P) (baseChangeEquiv ι R S M N bR bS)

open TensorProduct in
lemma baseChangeEquiv'_apply_basis {ι R S M N : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [DecidableEq ι]
    {P : Type*} [Ring P] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    (bR : Module.Basis ι R M) (bS : Module.Basis ι S N) (i : ι) (p : P) :
    baseChangeEquiv' ι R S M N bR bS P (p ⊗ₜ bR i) = p ⊗ₜ bS i := by
  simp [baseChangeEquiv', baseChangeEquiv_apply_basis]

open TensorProduct in
lemma baseChangeEquiv'_apply {ι R S M N : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [DecidableEq ι]
    {bR : Module.Basis ι R M} {bS : Module.Basis ι S N}
    (P : Type*) [Ring P] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    (α : M →ₛₗ[algebraMap R S] N)
    (hα : ∀ i, α (bR i) = bS i) (p : P) (m : M) :
    baseChangeEquiv' ι R S M N bR bS P (p ⊗ₜ m) = p ⊗ₜ α m := by
  nth_rewrite 1 2 [← bR.linearCombination_repr m]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, tmul_sum, map_sum]
  congr
  ext i
  simp [hα, tmul_smul, ← baseChangeEquiv'_apply_basis bR bS,
    LinearMapClass.map_smul_of_tower (baseChangeEquiv' ι R S M N bR bS P) ((bR.repr m) i)]

end Module.Basis

end defs
