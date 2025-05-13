import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Abstract -- abstract Hecke ops
import FLT.AutomorphicForm.QuaternionAlgebra.Defs -- definitions of automorphic forms
import FLT.QuaternionAlgebra.NumberField -- rigidifications of quat algs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
#check Subgroup.map (Units.map r.symm.toMonoidHom) (GL2.TameLevel S)

open scoped TensorProduct

variable {F D} in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- U1(S) -/
noncomputable abbrev U1 : Subgroup (D ⊗[F] (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))ˣ :=
  Subgroup.map (Units.map r.symm.toMonoidHom) (GL2.TameLevel S)

variable (R : Type*) [CommRing R]

def HeckeOperatorT : WeightTwoAutomorphicFormOfLevel (U1 r S) R →ₗ[R]
    WeightTwoAutomorphicFormOfLevel (U1 r S) R :=
  let g : (D ⊗[F] (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))ˣ := sorry
  sorry -- AbstractHeckeOperator.HeckeOperator _ (U1 r S) (U1 r S) sorry
