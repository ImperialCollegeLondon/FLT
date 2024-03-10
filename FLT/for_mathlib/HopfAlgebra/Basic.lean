import Mathlib.RingTheory.HopfAlgebra
import FLT.for_mathlib.Coalgebra.Monoid
import FLT.for_mathlib.Coalgebra.TensorProduct


open TensorProduct BigOperators

namespace HopfAlgebra

variable (R : Type*) [CommSemiring R]

section noncommutative

variable (A : Type*) [Semiring A] [HopfAlgebra R A]

variable {R A}

lemma antipode_repr {ι : Type*} (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul a = ∑ i in ℐ, Δ₁ i ⊗ₜ[R] Δ₂ i) :
    ∑ i in ℐ, antipode (R := R) (Δ₁ i) * Δ₂ i = algebraMap R A (Coalgebra.counit a) := by
  have := mul_antipode_rTensor_comul_apply (R := R) a
  rw [repr, map_sum, map_sum] at this
  exact this

lemma antipode_repr_eq_smul {ι : Type*} (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul a = ∑ i in ℐ, Δ₁ i ⊗ₜ[R] Δ₂ i) :
    ∑ i in ℐ, antipode (R := R) (Δ₁ i) * Δ₂ i = (Coalgebra.counit a : R) • (1 : A) := by
  rw [antipode_repr (repr := repr), Algebra.smul_def, mul_one]

lemma antipode_repr' {ι : Type*} (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul a = ∑ i in ℐ, Δ₁ i ⊗ₜ[R] Δ₂ i) :
    ∑ i in ℐ, Δ₁ i * antipode (R := R) (Δ₂ i) = algebraMap R A (Coalgebra.counit a) := by
  have := mul_antipode_lTensor_comul_apply (R := R) a
  rw [repr, map_sum, map_sum] at this
  exact this

lemma antipode_repr_eq_smul' {ι : Type*} (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul a = ∑ i in ℐ, Δ₁ i ⊗ₜ[R] Δ₂ i) :
    ∑ i in ℐ, Δ₁ i * antipode (R := R) (Δ₂ i) = (Coalgebra.counit a : R) • 1 := by
  rw [antipode_repr' (repr := repr), Algebra.smul_def, mul_one]

lemma antipode_mul_id : antipode (R := R) (A := A) * LinearMap.id = 1 := by
  ext x
  simpa [LinearPoint.mul_repr (repr := Coalgebra.comul_repr x)] using
    antipode_repr (repr := Coalgebra.comul_repr x)

lemma id_mul_antipode : LinearMap.id * antipode (R := R) (A := A) = 1 := by
  ext x
  simpa [LinearPoint.mul_repr (repr := Coalgebra.comul_repr x)] using
    antipode_repr' (repr := Coalgebra.comul_repr x)

lemma antipode_unique {T : LinearPoint R A A} (h : T * LinearMap.id = 1) :
    T = antipode :=
  left_inv_eq_right_inv (M := LinearPoint R A A) h id_mul_antipode


lemma antipode_unique' {T : LinearPoint R A A} (h : LinearMap.id * T = 1) :
    T = antipode :=
  left_inv_eq_right_inv (M := LinearPoint R A A) antipode_mul_id h |>.symm

lemma antipode_one : antipode (R := R) (A := A) 1 = 1 := by
  simpa using antipode_repr (R := R) (A := A) 1 {0} (fun _ ↦ 1) (fun _ ↦ 1)
    (by simp only [Bialgebra.comul_one, Finset.sum_const, Finset.card_singleton, one_smul]; rfl)

lemma antipode_anticommute (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) b * antipode (R := R) a := by
  let α : LinearPoint R (A ⊗[R] A) A := antipode ∘ₗ (LinearMap.mul' R A)
  let β : LinearPoint R (A ⊗[R] A) A := LinearMap.mul' R A ∘ₗ map antipode antipode ∘ₗ
    TensorProduct.comm R A A

  suffices α = β from congr($this (a ⊗ₜ b))

  apply left_inv_eq_right_inv (a := LinearMap.mul' R A)
  · ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearPoint.mul_repr (repr :=
        Coalgebra.TensorProduct.comul_apply_repr'' (repr_a := Coalgebra.comul_repr (R := R) a)
          (repr_b := Coalgebra.comul_repr (R := R) b)),
      LinearMap.coe_comp, Function.comp_apply, LinearMap.mul'_apply, LinearPoint.one_def,
      Coalgebra.TensorProduct.counit_def, LinearEquiv.coe_coe, map_tmul, lid_tmul, smul_eq_mul,
      Algebra.linearMap_apply, α, ← Bialgebra.counit_mul, Coalgebra.TensorProduct.comul_def]
    apply antipode_repr
    simpa only [Bialgebra.comul_mul, Coalgebra.comul_repr (a := a), Coalgebra.comul_repr (a := b),
      Finset.mul_sum, Finset.sum_mul, Algebra.TensorProduct.tmul_mul_tmul, Finset.sum_product] using
      Finset.sum_comm

  · ext a b
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearPoint.mul_repr (repr :=
        Coalgebra.TensorProduct.comul_apply_repr'' (repr_a := Coalgebra.comul_repr (R := R) a)
          (repr_b := Coalgebra.comul_repr (R := R) b)),
      LinearMap.mul'_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, comm_tmul,
      map_tmul, show ∀ a b c d : A, a * b * (c * d) = a * (b * c) * d by intros; group,
      Finset.sum_product, ← Finset.sum_mul, ← Finset.mul_sum,
      antipode_repr_eq_smul' (repr := Coalgebra.comul_repr b), LinearPoint.one_def,
      Coalgebra.TensorProduct.counit_def, lid_tmul, smul_eq_mul, Algebra.linearMap_apply,
      _root_.map_mul, β, Algebra.mul_smul_comm, mul_one, Algebra.smul_mul_assoc, ← Finset.smul_sum,
      antipode_repr_eq_smul' (repr := Coalgebra.comul_repr a), ← mul_smul, mul_comm]
    simp [Algebra.smul_def]

end noncommutative

section commutative

variable (A L : Type*) [CommSemiring A] [HopfAlgebra R A] [CommSemiring L] [Algebra R L]

variable {R A}

/--
If `A` is a commutative `R`=hopf algebra, then antipodal map is an algebra homomorphism
-/
@[simps!]
def antipodeAlgHom : A →ₐ[R] A := AlgHom.ofLinearMap antipode antipode_one fun a b ↦ by
  rw [antipode_anticommute, mul_comm]

namespace AlgHomPoint

noncomputable instance instGroup : Group (AlgHomPoint R A L) where
  inv f := f.comp antipodeAlgHom
  mul_left_inv f := AlgHom.ext fun x ↦ by
    simp only [AlgHomPoint.mul_repr (repr := Coalgebra.comul_repr x), AlgHom.comp_apply,
      antipodeAlgHom_apply, ← f.map_mul, ← map_sum, f.commutes, Algebra.ofId_apply,
      antipode_repr (repr := Coalgebra.comul_repr x), AlgHomPoint.one_def,
      Bialgebra.counitAlgHom_apply]

end AlgHomPoint

lemma antipodeAlgHom_inv : antipodeAlgHom⁻¹ = AlgHom.id R A :=
  inv_eq_iff_mul_eq_one.mpr <| AlgHom.ext fun x ↦ congr($(antipode_mul_id) x)

lemma antipodeAlgHom_mul_id : antipodeAlgHom * AlgHom.id R A = 1 :=
  AlgHom.ext fun _ ↦ congr($(antipode_mul_id) _)


lemma id_mul_antipodeAlgHom : AlgHom.id R A * antipodeAlgHom = 1 :=
  AlgHom.ext fun _ ↦ congr($(id_mul_antipode) _)

lemma antipodeAlgHom_square : antipodeAlgHom.comp antipodeAlgHom = AlgHom.id R A := by
  suffices antipodeAlgHom * (antipodeAlgHom.comp antipodeAlgHom) = (1 : AlgHomPoint R A A) by
    conv_rhs at this => rw [← antipodeAlgHom_mul_id]
    simpa only [mul_right_inj] using this
  ext a
  simp_rw [AlgHomPoint.mul_repr (repr := Coalgebra.comul_repr a),
    AlgHom.coe_comp, Function.comp_apply, ← antipodeAlgHom.map_mul, ← map_sum,
    antipodeAlgHom_apply, antipode_repr_eq_smul' (repr := Coalgebra.comul_repr a), map_smul,
    antipode_one, Algebra.smul_def, mul_one]
  rfl

/--
Then antipode map is an algebra equivalence.
-/
lemma antipodeAlgEquiv : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom antipodeAlgHom antipodeAlgHom antipodeAlgHom_square antipodeAlgHom_square

end commutative

end HopfAlgebra
