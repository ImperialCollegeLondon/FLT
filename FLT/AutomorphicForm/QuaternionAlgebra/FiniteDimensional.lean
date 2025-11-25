import FLT.AutomorphicForm.QuaternionAlgebra.Defs
import FLT.DivisionAlgebra.Finiteness
import FLT.Mathlib.Algebra.IsQuaternionAlgebra
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

namespace TotallyDefiniteQuaternionAlgebra

open IsDedekindDomain NumberField IsQuaternionAlgebra
open scoped TensorProduct TensorProduct.RightActions

-- let F be a number field
variable {F : Type*} [Field F] [NumberField F]
    -- and let D be a totally definite quaternion algebra over F
    {D : Type*} [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    (hD : IsTotallyDefinite F D)
-- Let K be a coefficient field
variable (K : Type*) [Field K]
    -- and let U, the level, be a subgroup of `(D ⊗ 𝔸_F^∞)ˣ`
    -- (which will be open in the theorem)
    {U : Subgroup (Dfx F D)}

open TotallyDefiniteQuaternionAlgebra

/--
Let `D/F` be a totally definite quaterion algebra over a totally real
field. Then the space of `K`-valued weight 2 level `U` quaternionic automorphic forms
for `Dˣ` is finite-dimensional over `K`.
-/
theorem WeightTwoAutomorphicForm.finiteDimensional [IsTotallyReal F]
    (hU : IsOpen (U : Set (Dfx F D))) :
    FiniteDimensional K (WeightTwoAutomorphicFormOfLevel U K) := by
  let H' : Subgroup (Dfx F D) := (incl₁ F D).range
  -- We will define a free K-module with a basis indexed by
  -- the elements of a double coset space which (in the totally
  -- definite case) is finite)
  let X := DoubleCoset.Quotient (Set.range (incl₁ F D)) U
  -- (the finiteness claim below is the nontrivial input to this proof)
  have h : Finite X := NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset F D hU
  -- We then define a linear map φ from V to the free K_module spanned by this finite set.
  -- V is a space of functions, and the map consists of evaluating
  -- a function on representatives given by the rep function above.
  let φ : (WeightTwoAutomorphicFormOfLevel U K) →ₗ[K] (X → K) := {
    toFun v x := v (Quot.out x),
    map_add' v₁ v₂ := rfl
    map_smul' c v := rfl
  }
  -- Since we have a linear map φ from V to a finite-dimensional space,
  -- it's enough to check that φ is injective. So say φ v₁ = φ v₂.
  apply FiniteDimensional.of_injective φ
  intro v₁ v₂ h
  ext d
  -- Show v₁ = v₂ because they agree on reps and the
  -- space is determined by those values
  let d' := Quot.out (Quot.mk _ d : X)
  -- Because d' is a representative for the double coset containing d
  obtain ⟨γ, u, hu, hd⟩ : ∃ γ : Dˣ, ∃ u ∈ U, d = (incl₁ F D γ) * d' * u := by
    have h_rel : (DoubleCoset.setoid H' U) d' d := Quotient.exact (Quotient.out_eq ⟦d⟧)
      -- Apply DoubleCoset.rel_iff to extract the witnesses
    rw [DoubleCoset.rel_iff] at h_rel
    obtain ⟨h, ⟨γ, rfl⟩, k, hk, h_eq⟩ := h_rel
    use γ, k, hk
  -- now it's all easy
  rw [hd, mul_assoc, v₁.left_invt γ (d' * u), v₂.left_invt γ (d' * u),
    WeightTwoAutomorphicFormOfLevel.right_invt v₁ d' ⟨u, hu⟩,
    WeightTwoAutomorphicFormOfLevel.right_invt v₂ d' ⟨u, hu⟩]
  exact congr_fun h (Quot.mk _ d)

end TotallyDefiniteQuaternionAlgebra
