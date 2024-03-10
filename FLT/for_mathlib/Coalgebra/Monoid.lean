/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Yanqiao Zhou, Jujian Zhang
-/


-- import Mathlib.Tactic
import Mathlib.RingTheory.TensorProduct
import FLT.for_mathlib.Coalgebra.Sweedler
import Mathlib.RingTheory.HopfAlgebra

-- open Function
-- open scoped TensorProduct

-- set_option maxHeartbeats 5000000
-- set_option linter.unusedVariables false

/-!
# Algebra and Linear Homomorphisms of Bialgebras, Coalgebras and Algebras
The first part of this files provides proofs of all the Algebra homomorphism from a
R-Bialgebra A to a Commutative R-Algebra L (defined as Points R A L) forms a monoid with the binary
operation "*" defined by convolution product and "one" defined by the composition of unit of L and
counit of A ((Algebra.ofId R L).comp (Bialgebra.counitAlgHom R A)), while the second part proves
that all the linear homomorphisms from a R-Coalgebra C to a R-Algebra B also forms a monoid by
the linear convolution product and the identity "linone" defined by (one _ _ _).toLinearMap.

# Proof of  TensorProduct of two R-Bialgebras (A1 and A2) are R-Bialgebras
The third part of this file is a preparation of the proof of the Antipode of a Hopf R-Algebra is
indeed an antihomomorphism (namely S(ab) = S(b)*S(a)), to do that we defined α β: H ⊗[R] H →ₗ H
to be α : (a ⊗ b) ↦ S(ab) and β : (a ⊗ b) ↦ S(b)*S(a). But for that to work we need the fact that
H ⊗ H is a Bialgebra and we genralized it to the Bialgebra case (In fact, C ⊗ C is a Coalgebra
for C being R-Coalgebra but we kind of include that in our proof of Bialgebra).

# Proof of all Algebra Homomorphism from a Commutative Hopf Algebra to a R-Algebra forms a Group
The fourth part of the part proves that (Points R H L) is a group that inherits multiplication
and identity elements from the monoid structure proved in Part I with inverse given by f⁻¹ =
(S ∘ f). And to do that we need antipode is an antihomomorphism (hence under the condition of
commutativity, we have that the antipode is an Algebra Homomorphism), and we did that by showing
α * m = linone and m * β = linone where m is the multiplication of H. Therefore α = α * linone
= α * (m * β) = (α * m) * β = linone * β = β showing that the anipode S is indeed an
antihomomorphism in H, then everythings follows (proving the group axioms, etc.)

# Finishing the TO-DO list in Hopf Algebra Files
At the end of this file (some are proved within the previous parts), we proved that S² = id and S
is a Bijection when H is Commutative (the case where H is Co-Commutative is unproved yet) and the
proof of the uniqueness of antipode is in the proof of LinPoints forms a monoid named as
anti_unique.

## Main declarations
- `Points.Points R A L` is all the R-Algebra Homomorphisms A →ₐ[R] L
- `Points.Pointmul_assoc` is the associativity of R-Algebra Homomorphisms in `Points R A L` under
  convolution product "*".
- `HopfPoints.LinPoints R C B` is all the R-Linear Maps C →ₗ[R] B where C is R-Coalgbra
  and B is R-Algebra
- `HopfPoints.mul_id_val`: id_H * S = linone under linear convolution product
- `HopfPoints.id_mul_val`: S * id_H = linone under linear convolution product
- `HopfPoints.UniquenessAnti` : Any T : H →ₗ H, if T * id_H = id_H * T = linone, then
  T = antipode (uniqueness of antipode).
- `HopfPoints.comul_repr` is the seedler notation for comultiplication for R-Coalgebras, that is
  ∀ x ∈ C, comul x can be expressed as ∑ i in I, x1 i ⊗ x2 i
- `HopfPoints.αmul_eqone`: α * m = linone
- `HopfPoints.mulβ_eqone`: m * β = linone
- `HopfPoints.antihom` : S(ab) = S(b) * S(a)
- `HopfPoints.antipodemul` : Under a Commutative Hopf Algebra H, S(ab) = S(a) * S(b)
- `HopfPoints.S2isid` : S² = id_H
- `HopfPoints.bijectiveAntipode` : S is bijection.

## References
* <https://en.wikipedia.org/wiki/Hopf_algebra>
* Christian Kassel "Quantum Groups" (Springer GTM), around Prop III.3.1, Theorem III.3.4 etc.
* Dr.Adrian de Jesus Celestino Rodriguez "Cumulants in Non-commutative Probability via Hopf
  Algebras", 2022
-/

open TensorProduct BigOperators LinearMap

section Coalgebra

/--
A linear point is a linear map from `A` to `L` where `A` is an `R`-colagebra and `L` an `R`-algebra.
We introduce this abbreviation is to prevent instance clashing when we put a monnoid structure on
these linear points with convolution product.

The confusion arise when we consider automorphism, for example `A →ₗ[R] A` already has a `mul` by
composition.
-/
abbrev LinearPoint (R A L : Type*)
    [CommSemiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid L] [Module R L] :=
  A →ₗ[R] L

namespace LinearPoint

variable {R A L : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
variable [Semiring L] [Algebra R L]

instance : FunLike (LinearPoint R A L) A L :=
  inferInstanceAs <| FunLike (A →ₗ[R] L) A L

instance : LinearMapClass (LinearPoint R A L) R A L :=
  inferInstanceAs <| LinearMapClass (A →ₗ[R] L) R A L

variable  (φ ψ χ : LinearPoint R A L)

/--
`A -comul-> A ⊗ A -φ ⊗ ψ-> L ⊗ L -mul> L` is convolution product of `φ` and `ψ`.
If `comul x = ∑ aᵢ ⊗ bᵢ`, then `(φ ⋆ ψ)(x) = ∑ φ(aᵢ) × ψ(bᵢ)`, hence the name convolution.
-/
noncomputable def mul : LinearPoint R A L :=
  LinearMap.mul' _ _ ∘ₗ TensorProduct.map φ ψ ∘ₗ Coalgebra.comul

lemma mul_repr' {ι : Type* } (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul (R := R) a = ∑ i in ℐ, Δ₁ i ⊗ₜ Δ₂ i) :
    φ.mul ψ a = ∑ i in ℐ, φ (Δ₁ i) * ψ (Δ₂ i) := by
  simp only [mul, comp_apply, repr, map_sum, map_tmul, mul'_apply]

/--
`A -counit-> R -algebraMap-> L` is the unit with respect to convolution product.
-/
def one : LinearPoint R A L :=
  Algebra.linearMap R L ∘ₗ Coalgebra.counit

instance : One (LinearPoint R A L) where
  one := one

lemma one_def : (1 : LinearPoint R A L) = Algebra.linearMap R L ∘ₗ Coalgebra.counit := rfl

noncomputable instance : Mul (LinearPoint R A L) where
  mul := mul

lemma mul_repr {ι : Type* } (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul (R := R) a = ∑ i in ℐ, Δ₁ i ⊗ₜ Δ₂ i) :
    (φ * ψ) a = ∑ i in ℐ, φ (Δ₁ i) * ψ (Δ₂ i) :=
  mul_repr' _ _ a ℐ Δ₁ Δ₂ repr

lemma mul_assoc' : φ * ψ * χ = φ * (ψ * χ) := LinearMap.ext fun x ↦ by
  simp only [show
      (φ * ψ) * χ =
        LinearMap.mul' _ _ ∘ₗ
          (LinearMap.mul' _ _).rTensor _ ∘ₗ
            (map (map _ _) _) ∘ₗ Coalgebra.comul.rTensor _ ∘ₗ Coalgebra.comul
      by simp only [← comp_assoc, map_comp_rTensor, rTensor_comp_map]; rfl,
    mul', comp_apply, Coalgebra.comul_repr, map_sum, rTensor_tmul, sum_tmul, map_tmul, lift.tmul,
    mul_apply', mul_assoc,
    show
      φ * (ψ * χ) =
        LinearMap.mul' _ _ ∘ₗ
          (LinearMap.mul' _ _).lTensor _ ∘ₗ
            (map _ (map _ _)) ∘ₗ Coalgebra.comul.lTensor _ ∘ₗ Coalgebra.comul
      by simp only [← comp_assoc, map_comp_lTensor, lTensor_comp_map]; rfl,
    ← Coalgebra.coassoc, LinearEquiv.coe_coe, assoc_tmul, lTensor_tmul]

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

attribute [deprecated] mul_assoc' mul_one' one_mul' mul_repr'

end LinearPoint

end Coalgebra

section Bialgebra

/--
An algebra homomorphism point is an algebra homorphism from `A` to `L` where `A` is an `R`-biagebra
and `L` an `R`-algebra. We introduce this abbreviation is to prevent instance clashing when we put a
monnoid structure on these algebra homomorphism points with convolution product.

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
/--
`A -counit-> R -algebraMap-> L` is the unit with respect to convolution product.
-/
noncomputable def one : AlgHomPoint R A L :=
  Algebra.ofId R L |>.comp <| Bialgebra.counitAlgHom R A

noncomputable instance : One (AlgHomPoint R A L) where
  one := one

lemma one_def : (1 : AlgHomPoint R A L) = (Algebra.ofId R L).comp (Bialgebra.counitAlgHom R A) :=
  rfl

noncomputable instance : Mul (AlgHomPoint R A L) where
  mul := mul

lemma mul_assoc' : φ * ψ * χ = φ * (ψ * χ) := by
  ext
  exact congr($(mul_assoc φ.toLinearPoint ψ.toLinearPoint χ.toLinearPoint) _)

lemma mul_one' : φ * 1 = φ := by
  ext; exact congr($(mul_one φ.toLinearPoint) _)

lemma one_mul' : 1 * φ = φ := show mul one φ = φ by
  ext; exact congr($(one_mul φ.toLinearPoint) _)

noncomputable instance instMonoid : Monoid (AlgHomPoint R A L) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'

lemma mul_repr {ι : Type* } (a : A) (ℐ : Finset ι) (Δ₁ Δ₂ : ι → A)
    (repr : Coalgebra.comul (R := R) a = ∑ i in ℐ, Δ₁ i ⊗ₜ Δ₂ i) :
    (φ * ψ) a = ∑ i in ℐ, φ (Δ₁ i) * ψ (Δ₂ i) :=
  LinearPoint.mul_repr _ _ a ℐ Δ₁ Δ₂ repr

attribute [deprecated] mul_assoc' mul_one' one_mul'

end AlgHomPoint
