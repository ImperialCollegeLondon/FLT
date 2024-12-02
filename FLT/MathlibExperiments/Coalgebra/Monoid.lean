/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Yanqiao Zhou, Jujian Zhang
-/

import Mathlib.RingTheory.TensorProduct.Basic
import FLT.MathlibExperiments.Coalgebra.Sweedler
import Mathlib.RingTheory.HopfAlgebra

/-!
# Monoid structure on linear maps and algebra homomorphism

Let `A` be an `R`-coalgebra and `L` an `R`-algebra. Then the set of `R`-linear maps `A →ₗ[R] L`
from `A` to `L` can be endowed a monoid structure where:

* the identity is defined as `A --counit--> R --algebraMap--> L`
* multiplication `f * g` is defined as `A --comul--> A ⊗ A --f ⊗ g--> L ⊗ L --multiplication--> L`
  for R-linear maps `f` and `g`.

Since `comul x = ∑ yᵢ ⊗ zᵢ` implies `(f * g) x = ∑ f(yᵢ) g(zᵢ)`, this multiplication is often called
convolution.

If furthermore `A` is an `R`-bialgebra, then the subset of `R`-algebra morphisms `A →ₐ[R] L` from
`A` to `L` is closed under the multiplication and is hence a submonoid.

## References
* <https://en.wikipedia.org/wiki/Hopf_algebra>
* Christian Kassel "Quantum Groups" (Springer GTM), around Prop III.3.1, Theorem III.3.4 etc.
* Dr.Adrian de Jesus Celestino Rodriguez "Cumulants in Non-commutative Probability via Hopf
  Algebras", 2022
-/

open TensorProduct BigOperators LinearMap

section Coalgebra

-- Note that using an `abbrev` here creates a diamond in the case `A = L`, when there
-- is already a multiplication on `A →ₗ[R] A`, defined by composition.

/--
Let `A` be an `R`-coalgebra and `L` an `R`-algebra. An `L`-linear point of `A`
is an `R`-linear map from `A` to `L`.
-/
abbrev LinearPoint (R A L : Type*)
    [CommSemiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid L] [Module R L] :=
  A →ₗ[R] L

namespace LinearPoint

variable {R A L : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
variable [Semiring L] [Algebra R L]

variable  (φ ψ χ : LinearPoint R A L)

/--
`A -comul-> A ⊗ A -φ ⊗ ψ-> L ⊗ L -mul> L` is convolution product of `φ` and `ψ`.
If `comul x = ∑ aᵢ ⊗ bᵢ`, then `(φ ⋆ ψ)(x) = ∑ φ(aᵢ) × ψ(bᵢ)`, hence the name convolution.
-/
noncomputable def mul : LinearPoint R A L :=
  LinearMap.mul' _ _ ∘ₗ TensorProduct.map φ ψ ∘ₗ Coalgebra.comul

noncomputable instance : Mul (LinearPoint R A L) where
  mul := mul

lemma mul_def (φ ψ : LinearPoint R A L) :
    φ * ψ = LinearMap.mul' _ _ ∘ₗ TensorProduct.map φ ψ ∘ₗ Coalgebra.comul := rfl

lemma mul_repr' {ι : Type* } (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul (R := R) a = ∑ i in ℐ, Δ₁ i ⊗ₜ Δ₂ i) :
    φ.mul ψ a = ∑ i in ℐ, φ (Δ₁ i) * ψ (Δ₂ i) := by
  simp only [mul, comp_apply, repr, map_sum, map_tmul, mul'_apply]

lemma mul_repr {ι : Type* } (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul (R := R) a = ∑ i in ℐ, Δ₁ i ⊗ₜ Δ₂ i) :
    (φ * ψ) a = ∑ i in ℐ, φ (Δ₁ i) * ψ (Δ₂ i) :=
  mul_repr' _ _ a ℐ Δ₁ Δ₂ repr

lemma mul_assoc' : φ * ψ * χ = φ * (ψ * χ) := LinearMap.ext fun x ↦ by
  rw [show (φ * ψ) * χ =
        LinearMap.mul' _ _ ∘ₗ
          (LinearMap.mul' _ _).rTensor _ ∘ₗ
            (map (map _ _) _) ∘ₗ Coalgebra.comul.rTensor _ ∘ₗ Coalgebra.comul
      by simp only [← comp_assoc, map_comp_rTensor, rTensor_comp_map]; rfl]
  rw [show φ * (ψ * χ) =
        LinearMap.mul' _ _ ∘ₗ
          (LinearMap.mul' _ _).lTensor _ ∘ₗ
            (map _ (map _ _)) ∘ₗ Coalgebra.comul.lTensor _ ∘ₗ Coalgebra.comul
      by simp only [← comp_assoc, map_comp_lTensor, lTensor_comp_map]; rfl]
  simp only [mul', comp_apply, Coalgebra.comul_repr, map_sum, rTensor_tmul, sum_tmul, map_tmul,
    lift.tmul, mul_apply', mul_assoc, ← Coalgebra.coassoc, LinearEquiv.coe_coe, assoc_tmul,
    lTensor_tmul]

/--
`A --counit--> R --algebraMap--> L` is the unit with respect to convolution product.
-/
def one : LinearPoint R A L :=
  Algebra.linearMap R L ∘ₗ Coalgebra.counit

instance : One (LinearPoint R A L) where
  one := one

lemma one_def : (1 : LinearPoint R A L) = Algebra.linearMap R L ∘ₗ Coalgebra.counit := rfl

lemma mul_one' : φ * 1 = φ := show mul φ one = φ from LinearMap.ext fun _ ↦ by
  simp [show φ.mul one =
    LinearMap.mul' _ _ ∘ₗ φ.rTensor _ ∘ₗ (Algebra.linearMap _ _).lTensor _ ∘ₗ
      Coalgebra.counit.lTensor _ ∘ₗ Coalgebra.comul by
    delta one mul
    simp [← comp_assoc, ← map_comp, comp_id, id_comp]]

lemma one_mul' : 1 * φ = φ := show mul one φ = φ from LinearMap.ext fun _ ↦ by
  simp [show one.mul φ =
    LinearMap.mul' _ _ ∘ₗ φ.lTensor _ ∘ₗ (Algebra.linearMap _ _).rTensor _ ∘ₗ
      Coalgebra.counit.rTensor _ ∘ₗ Coalgebra.comul by
    delta one mul
    simp [← comp_assoc, ← map_comp, comp_id, id_comp]]

noncomputable instance instMonoid : Monoid (LinearPoint R A L) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'

attribute [deprecated mul_assoc (since := "2024-03-10")] mul_assoc'
attribute [deprecated mul_one (since := "2024-03-10")] mul_one'
attribute [deprecated one_mul (since := "2024-03-10")] one_mul'
attribute [deprecated mul_repr (since := "2024-03-10")] mul_repr'

end LinearPoint

end Coalgebra

section Bialgebra

/--
An algebra homomorphism point is an algebra homomorphism from `A` to `L` where `A` is an `R`-bialgebra
and `L` an `R`-algebra. We introduce this abbreviation is to prevent instance clashing when we put a
monoid structure on these algebra homomorphism points with convolution product.

This confusion happens when `A` and `L` are the same where default multiplication is composition.
-/
abbrev AlgHomPoint (R A L : Type*) [CommSemiring R] [Semiring A] [Bialgebra R A]
    [CommSemiring L] [Algebra R L] :=
  A →ₐ[R] L

namespace AlgHomPoint

variable  {R A L : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]
variable [CommSemiring L] [Algebra R L]

variable  (φ ψ χ : AlgHomPoint R A L)

/--
An algebra homomorphism is also a linear map
-/
abbrev toLinearPoint : LinearPoint R A L := φ.toLinearMap

/--
`A -comul-> A ⊗ A -φ ⊗ ψ-> L ⊗ L -mul> L` is convolution product of `φ` and `ψ`.
If `comul x = ∑ aᵢ ⊗ bᵢ`, then `(φ ⋆ ψ)(x) = ∑ φ(aᵢ) × ψ(bᵢ)`, hence the name convolution.
-/
noncomputable def mul : AlgHomPoint R A L :=
  Algebra.TensorProduct.lmul' R (S := L) |>.comp <|
    Algebra.TensorProduct.map φ ψ |>.comp <| Bialgebra.comulAlgHom R A

noncomputable instance : Mul (AlgHomPoint R A L) where
  mul := mul

lemma mul_def (φ ψ : AlgHomPoint R A L) :
    φ * ψ = (Algebra.TensorProduct.lmul' R (S := L) |>.comp <|
      Algebra.TensorProduct.map φ ψ |>.comp <| Bialgebra.comulAlgHom R A) := rfl

lemma mul_repr {ι : Type* } (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul (R := R) a = ∑ i in ℐ, Δ₁ i ⊗ₜ Δ₂ i) :
    (φ * ψ) a = ∑ i in ℐ, φ (Δ₁ i) * ψ (Δ₂ i) :=
  LinearPoint.mul_repr _ _ a ℐ Δ₁ Δ₂ repr

lemma mul_assoc' : φ * ψ * χ = φ * (ψ * χ) := by
  ext
  exact congr($(mul_assoc φ.toLinearPoint ψ.toLinearPoint χ.toLinearPoint) _)

/--
`A -counit-> R -algebraMap-> L` is the unit with respect to convolution product.
-/
noncomputable def one : AlgHomPoint R A L :=
  Algebra.ofId R L |>.comp <| Bialgebra.counitAlgHom R A

noncomputable instance : One (AlgHomPoint R A L) where
  one := one

lemma one_def : (1 : AlgHomPoint R A L) = (Algebra.ofId R L).comp (Bialgebra.counitAlgHom R A) :=
  rfl

lemma mul_one' : φ * 1 = φ := by
  ext; exact congr($(mul_one φ.toLinearPoint) _)

lemma one_mul' : 1 * φ = φ := show mul one φ = φ by
  ext; exact congr($(one_mul φ.toLinearPoint) _)

noncomputable instance instMonoid : Monoid (AlgHomPoint R A L) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'

attribute [deprecated mul_assoc (since := "2024-03-10")] mul_assoc'
attribute [deprecated mul_one (since := "2024-03-10")] mul_one'
attribute [deprecated one_mul (since := "2024-03-10")] one_mul'

section commutative_bialgebra

variable {A' : Type*} [CommSemiring A'] [Bialgebra R A']

lemma comp_one {A' : Type*} [CommSemiring A'] [Bialgebra R A']
    (f : AlgHomPoint R A' L) :
    f.comp (1 : AlgHomPoint R A' A') = 1 := by
  ext
  simp [one_def, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, map_smul, _root_.map_one]

end commutative_bialgebra

end AlgHomPoint
