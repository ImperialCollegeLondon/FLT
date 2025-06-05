import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free

/-

# Right module and algebra instances

This file enables you to write `open scoped TensorProduct.RightActions` and magically `A ⊗[R] B`
becomes a `B`-algebra as well as an `A`-algebra, and you get instances like
`[Module.Finite R A] → [Module.Finite B (A ⊗[R] B)]`.

Perhaps even more controversially, if `B` is a commutative topological ring and an `A`-algebra,
it will put a topological module structure on `M ⊗[A] B` for `M` an `A`-module.

Mathlib would not have this hack because `A ⊗[R] A` is now an `A`-algebra in two
different ways. But this situation will not arise in the cases where we use this,
and it's very convenient to open the scope temporarily in order to prove theorems
which can be used without the scope open.
-/

namespace TensorProduct.RightActions

noncomputable section semiring

variable (R S A B M : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M]
    [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B]

scoped instance : SMul S (M ⊗[R] S) where
  smul s e := TensorProduct.comm _ _ _ (s • (TensorProduct.comm _ _ _ e))

@[simp]
lemma smul_def (r : S) (m : M ⊗[R] S) :
    r • m = (TensorProduct.comm _ _ _).symm (r • (TensorProduct.comm _ _ _ m)) := rfl

scoped instance : Module S (M ⊗[R] S) where
  one_smul _ := by simp
  mul_smul := by simp [mul_smul]
  smul_zero := by simp
  smul_add := by simp
  add_smul := by simp [add_smul]
  zero_smul := by simp

scoped instance : Algebra S (B ⊗[R] S) where
  algebraMap := Algebra.TensorProduct.includeRight.toRingHom
  commutes' s bs := by
    induction bs with
    | zero => simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, mul_zero, zero_mul]
    | tmul x y =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, mul_comm]
    | add x y _ _ =>
        simp_all only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, mul_add, add_mul]
  smul_def' s bs := by
    induction bs with
    | zero => simp only [smul_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, mul_zero]
    | tmul b s =>
        simp only [smul_def, TensorProduct.comm_tmul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [TensorProduct.smul_tmul']
        simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
    | add x y hx hy =>
        simp_all only [smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, smul_add, ← hx, ← hy, mul_add]

@[simp] lemma algebraMap_eval (s : S) : algebraMap S (B ⊗[R] S) s = 1 ⊗ₜ s := rfl

/-- The A-algebra isomorphism A ⊗ B = B ⊗ A, available in the `TensorProduct.RightActions` scope. -/
@[simps! apply symm_apply]
def Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[A] B ⊗[R] A where
  __ := _root_.Algebra.TensorProduct.comm R A B
  commutes' _ := rfl

variable {A B} in
@[simp] lemma Algebra.TensorProduct.comm_apply_tmul (a : A) (b : B) :
    Algebra.TensorProduct.comm R A B (a ⊗ₜ b) = b ⊗ₜ a := rfl

@[simp] lemma Algebra.TensorProduct.comm_symm_apply_tmul (b : B) (a : A) :
    (Algebra.TensorProduct.comm R A B).symm (b ⊗ₜ a) = a ⊗ₜ b := rfl

/-- The A-module isomorphism A ⊗ M = M ⊗ A, available in the `TensorProduct.RightActions` scope. -/
@[simps! apply symm_apply]
def Module.TensorProduct.comm : A ⊗[R] M ≃ₗ[A] M ⊗[R] A where
  __ := (_root_.TensorProduct.comm R A M).toAddEquiv
  map_smul' a am := by
    induction am with
    | zero => simp only [smul_zero, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      LinearEquiv.coe_coe, map_zero, RingHom.id_apply]
    | tmul x y =>
        simp only [smul_tmul', smul_eq_mul, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, comm_tmul, RingHom.id_apply, smul_def, comm_symm_tmul]
    | add x y hx hy =>
      simp_all only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        RingHom.id_apply, smul_def, smul_add, map_add]

variable {A N} in
@[simp] lemma Module.TensorProduct.comm_apply_tmul (a : A) (m : M) :
    Module.TensorProduct.comm R A M (a ⊗ₜ m) = m ⊗ₜ a := rfl

@[simp] lemma Module.TensorProduct.comm_symm_apply_tmul (m : M) (a : A) :
    (Module.TensorProduct.comm R A M).symm (m ⊗ₜ a) = a ⊗ₜ m := rfl

scoped instance [Module.Finite R M] : Module.Finite A (M ⊗[R] A) :=
  Module.Finite.equiv (Module.TensorProduct.comm R A M)

scoped instance [Module.Free R M] : Module.Free A (M ⊗[R] A) :=
  Module.Free.of_equiv (Module.TensorProduct.comm R A M)

scoped instance : IsScalarTower R A (M ⊗[R] A) where
  smul_assoc r a ma := by simp

/-- The module topology on a right algebra. -/
scoped instance [TopologicalSpace A] : TopologicalSpace (B ⊗[R] A) :=
  moduleTopology A (B ⊗[R] A)

scoped instance [TopologicalSpace A] : IsModuleTopology A (B ⊗[R] A) := ⟨rfl⟩

noncomputable abbrev LinearMap.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V →ₗ[R] W) : V ⊗[R] A →ₗ[A] W ⊗[R] A :=
  (Module.TensorProduct.comm R A W) ∘ₗ
    (_root_.LinearMap.baseChange A φ) ∘ₗ
    (Module.TensorProduct.comm R A V).symm

-- this should be in mathlib
-- theorem foo (R M N : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
--     [Module R M] [Module R N] (e : M ≃ₗ[R] N) : (e : M ≃+ N).symm = (e.symm: N ≃+ M) := rfl

noncomputable def AlgebraMap.baseChange (R : Type*) [CommRing R]
    (B C : Type*) [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : B →ₐ[R] C) : B ⊗[R] A →ₐ[A] C ⊗[R] A where
  __ := Algebra.TensorProduct.map φ (.id R A)
  commutes' a := by simp

end semiring

noncomputable section ring

variable (R A B : Type*) [CommRing R]
    [CommRing A] [Algebra R A]
    [Ring B] [Algebra R B]

scoped instance [TopologicalSpace A] [IsTopologicalRing A] [Module.Finite R B] :
    IsTopologicalRing (B ⊗[R] A) :=
  IsModuleTopology.Module.topologicalRing A _

scoped instance [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [Module.Finite R B] :
    LocallyCompactSpace (B ⊗[R] A) := IsModuleTopology.locallyCompactSpaceOfFinite A

end ring -- section

end TensorProduct.RightActions
#min_imports
