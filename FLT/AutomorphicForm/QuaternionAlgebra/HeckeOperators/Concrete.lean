import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Abstract -- abstract Hecke ops
import FLT.AutomorphicForm.QuaternionAlgebra.Defs -- definitions of automorphic forms
import FLT.QuaternionAlgebra.NumberField -- rigidifications of quat algs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.AutomorphicForm.GL2.HeckeOperators.Matrix -- for (π 0; 0 1)
import FLT.Mathlib.Topology.Algebra.RestrictedProduct
/-

# Concrete Hecke operators

Hecke operators for spaces of automorphic forms on totally definite quaternion algebras.

-/

open NumberField IsQuaternionAlgebra.NumberField IsDedekindDomain

-- let F be a totally real number field
variable (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]

-- Let D/F be a quaternion algebra
variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

-- Let r be a rigidification of D, which is a collection of isomorphisms D ⊗ Fᵥ = M₂(Fᵥ)
-- for all finite places v of F, compatible with the adelic structure (i.e. inducing
-- an isomorphism D ⊗_F 𝔸_F^f = M₂(𝔸_F^f))
variable (r : Rigidification F D)

-- Let S be a finite set of finite plaes of F (the level)
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- let P be a good prime
variable {P : HeightOneSpectrum (𝓞 F)} (hP : P ∉ S)

open TotallyDefiniteQuaternionAlgebra
-- let's do T_P : S_2^D(U_1(S)) -> S_2^D(U_1(S))
namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm

open IsDedekindDomain.HeightOneSpectrum

-- attribute [local instance] Algebra.TensorProduct.rightAlgebra in
-- #check Subgroup.map (Units.map r.symm.toMonoidHom) (GL2.TameLevel S)

open scoped TensorProduct

variable {F D} in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- U1(S) -/
noncomputable abbrev U1 : Subgroup (D ⊗[F] (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))ˣ :=
  Subgroup.map (Units.map r.symm.toMonoidHom) (GL2.TameLevel S)

variable (R : Type*) [CommRing R]

namespace HeckeOperator

variable {F D S} in
set_option maxSynthPendingDepth 1 in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The Hecke operator T_v as an R-linear map from R-valued quaternionic weight 2
automorphic forms of level U_1(S).
-/
noncomputable def T (v : HeightOneSpectrum (𝓞 F)) :
    WeightTwoAutomorphicFormOfLevel (U1 r S) R →ₗ[R]
    WeightTwoAutomorphicFormOfLevel (U1 r S) R :=
  letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
  let g : (D ⊗[F] (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))ˣ :=
    Units.map r.symm.toMonoidHom (Matrix.GeneralLinearGroup.diagonal
    ![FiniteAdeleRing.localUniformiserUnit F v, 1])
  AbstractHeckeOperator.HeckeOperator (R := R) g (U1 r S) (U1 r S) sorry

variable {F D} in
set_option maxSynthPendingDepth 1 in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The Hecke operator U_{v,α} associated to the matrix (α 0;0 1) at v,
considered as an R-linear map from R-valued quaternionic weight 2
automorphic forms of level U_1(S). Here α is a nonzero element of 𝓞ᵥ.
We do not demand the condition v ∈ S, the bad primes, but this operator
should only be used in this setting. See also `T r v` for the good primes.
-/
@[nolint unusedArguments] -- this can be removed when the sorries are filled in
-- but not before because it breaks linting
noncomputable def U {v : HeightOneSpectrum (𝓞 F)}
    (α : v.adicCompletionIntegers F) (hα : α ≠ 0) :
    WeightTwoAutomorphicFormOfLevel (U1 r S) R →ₗ[R]
    WeightTwoAutomorphicFormOfLevel (U1 r S) R :=
  letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
  let g : (D ⊗[F] (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))ˣ :=
    Units.map r.symm.toMonoidHom (Matrix.GeneralLinearGroup.diagonal
    ![FiniteAdeleRing.localUnit F ⟨(α : v.adicCompletion F),
    (α : v.adicCompletion F)⁻¹,
    sorry, sorry⟩, 1])
  AbstractHeckeOperator.HeckeOperator (R := R) g (U1 r S) (U1 r S) sorry

lemma _root_.Ne.mul {M₀ : Type*} [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}
  (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := mul_ne_zero ha hb

lemma U_mul {v : HeightOneSpectrum (𝓞 F)}
    {α β : v.adicCompletionIntegers F} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (U r S R α hα ∘ₗ U r S R β hβ) =
    U r S R (α * β) (hα.mul hβ) := by
  sorry

lemma U_comm {v : HeightOneSpectrum (𝓞 F)}
    {α β : v.adicCompletionIntegers F} (hα : α ≠ 0) (hβ : β ≠ 0) :
    U r S R α hα ∘ₗ U r S R β hβ =
    U r S R β hβ ∘ₗ U r S R α hα := by
  rw [U_mul, U_mul]
  congr 1
  rw [mul_comm]

end HeckeOperator

open HeckeOperator

/-- `HeckeAlgebra F D r S R` is the Hecke algebra associated to the weight 2
`R`-valued automorphic forms associated to the discriminant 1 totally definite
quaternion algebra `D` over the totally real field `F`, of level `U₁(S)` where `S` is
a finite set of nonzero primes `v` of `𝓞 F`. To make sense of this definition we choose
a rigidification `r`, that is, a fixed `𝔸_F^∞`-linear
isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`, enabling us to define level structures and
Hecke operators `Tᵥ` and `Uᵥ` using 2x2 matrices.

Details: `U₁(S)` is the subgroup of `(D ⊗[F] 𝔸_F^∞)ˣ` associated, via `r`, to the
matrices which are in `GL₂(𝓞ᵥ)` for all `v ∉ S` and which are of the form
`(a *; 0 a)` mod `v` for all `v ∈ S`. The Hecke algebra is defined to be the
sub-`R`-algebra of the weight 2 forms of level `U₁(S)` generated by the following
two kinds of Hecke operators: first there are the operators
`Tᵥ` associated to the matrices `(ϖᵥ 0; 0 1)` for `v ∉ S` (here `ϖᵥ ∈ 𝔸_F^∞` is a local
uniformiser supported at `v`). Second, there are the Hecke operators `Uᵥ,ₐ`
for `v ∈ S` and `0 ≠ αᵥ ∈ 𝓞ᵥ`, associated the matries `(αᵥ 0; 0 1)`.
These slightly nonstandard Hecke operators satisfy `Uᵥ,ₛ * Uᵥ,ₜ = Uᵥ,ₛₜ`
and in particular this Hecke algebra is commutative (Hecke operators supported
at distinct primes commute because the decomposition of the double cosets
into single cosets can be done purely locally).
-/
def HeckeAlgebra : Type _ :=
  (Algebra.adjoin R ({T r R v | v ∉ S} ∪
  {φ | ∃ (v : HeightOneSpectrum (𝓞 F)) (_hv : v ∈ S)
         (α : v.adicCompletionIntegers F) (hα : α ≠ 0), φ = U r S R α hα}) :
    Subalgebra R (WeightTwoAutomorphicFormOfLevel (U1 r S) R →ₗ[R]
      WeightTwoAutomorphicFormOfLevel (U1 r S) R))

namespace HeckeAlgebra

noncomputable instance instRing :
    Ring (HeckeAlgebra F D r S R) := inferInstanceAs <|
  Ring (Algebra.adjoin R _ : Subalgebra R (WeightTwoAutomorphicFormOfLevel (U1 r S) R →ₗ[R]
      WeightTwoAutomorphicFormOfLevel (U1 r S) R))

noncomputable instance instAlgebra :
    Algebra R (HeckeAlgebra F D r S R) := inferInstanceAs <|
  Algebra R (Algebra.adjoin R _ : Subalgebra R (WeightTwoAutomorphicFormOfLevel (U1 r S) R →ₗ[R]
      WeightTwoAutomorphicFormOfLevel (U1 r S) R))

noncomputable instance instCommRing :
    CommRing (HeckeAlgebra F D r S R) where
  __ := instRing F D r S R
  mul_comm := sorry

/-- The Hecke operator Tᵥ as an element of the Hecke algebra. -/
noncomputable def T (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) : HeckeAlgebra F D r S R :=
  ⟨HeckeOperator.T r R v, by
    apply Algebra.subset_adjoin
    left
    use v⟩

/-- The Hecke operator Uᵥ,ₐ as an element of the Hecke algebra. -/
noncomputable def U (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) (α : v.adicCompletionIntegers F)
    (hα : α ≠ 0) : HeckeAlgebra F D r S R :=
  ⟨HeckeOperator.U r S R α hα, by
    apply Algebra.subset_adjoin
    right
    use v, hv, α, hα⟩

end HeckeAlgebra

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm
