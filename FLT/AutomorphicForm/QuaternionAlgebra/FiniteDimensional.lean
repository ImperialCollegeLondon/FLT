import FLT.AutomorphicForm.QuaternionAlgebra.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Data.Set.Finite.Basic
import FLT.DivisionAlgebra.Finiteness

namespace TotallyDefiniteQuaternionAlgebra

open IsDedekindDomain NumberField IsQuaternionAlgebra
open scoped TensorProduct TensorProduct.RightActions

-- let F be a number field
variable {F : Type*} [Field F] [NumberField F]
    -- and let D be a totally definite quaternion algebra over F
    -- TODO the assumption that D is totally definite implies that
    -- D is a division ring, so we should be able to remove the
    -- [DivisionRing D] requirement.
    {D : Type*} [DivisionRing D] [Algebra F D] [IsQuaternionAlgebra F D]
    (hD : IsTotallyDefinite F D)
-- Let K be a coefficient field
variable (K : Type*) [Field K]
    -- and let U, the level, be a (compact) open subgroup of `(D ⊗ 𝔸_F^∞)ˣ`
    (U : Subgroup (Dfx (F:=F) (D:=D)))
    (hU : IsOpen (U : Set (Dfx (F:=F) (D:=D))))

open TotallyDefiniteQuaternionAlgebra


-- Then the space of K-valued weight 2 level U modular forms for Dˣ is finite-dimensional over K.
/-- The space of `K`-valued weight 2 level `U` quaternionic automorphic forms
for `Dˣ` is finite-dimensional over `K`.
-/
theorem WeightTwoAutomorphicForm.finiteDimensional
    {hU : IsOpen (U : Set (Dfx (F:=F) (D:=D)))} :
    FiniteDimensional K (WeightTwoAutomorphicFormOfLevel U K) := by
    let U' : Subgroup (Dfx F D) := U
    let H' : Subgroup (Dfx F D) := {
        carrier := Set.range (incl₁ F D),
        one_mem' := ⟨1, by simp⟩,
        mul_mem' := by
            rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
            exact ⟨a * b, by simp⟩,
        inv_mem' := by
            rintro _ ⟨a, rfl⟩
            exact ⟨a⁻¹, by simp⟩
    }
    -- We define a free K-module W with a basis indexed by
    -- the elements of a double coset space which (in the totally
    -- definite case) is finite)
    let X := Doset.Quotient (Set.range (incl₁ F D)) U'
    have h : Finite X :=
        NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset (K:=F) (D:=D) hU

    letI := Fintype.ofFinite X
    let m := Fintype.card X
    let W := Fin m → K
    let V := (WeightTwoAutomorphicFormOfLevel U K)

    let index := (Fintype.equivFin X : X ≃ Fin m)
    let rep : X → Dfx F D := Quot.out

    -- We then define a linear map φ from V to the finite-dimensional space W.
    -- V is a space of functions, and the map consists of evaluating
    -- a function on representatives given by the rep function above.
    let φ : V →ₗ[K] W :=
        {
        toFun := fun v i ↦ v.1.toFun (rep (index.symm i)),
        map_add' := by
            intros v₁ v₂
            ext i
            rfl
        map_smul' := by
            intros c v
            ext i
            rfl
        }
    -- Since we have a linear map φ from V to W and W is finite-dimensional,
    -- it's enough to check that φ is injective.
    have φ_injective : Function.Injective φ := by
        intro v₁ v₂ h
        let f₁ : WeightTwoAutomorphicForm F D K := v₁.1
        let f₂ : WeightTwoAutomorphicForm F D K := v₂.1
        -- Show v₁.toFun = v₂.toFun because they agree on reps and the
        -- space is determined by those values
        have fun_eq : ∀ d, f₁.toFun d = f₂.toFun d := by
            intro d
            let d' := rep (Quot.mk _ d)
            -- Because d' is a representative for the double coset containing d
            have hcoset : ∃ γ : Dˣ, ∃ u ∈ U, d = (incl₁ F D γ) * d' * u := by
                have h_rel : (Doset.setoid H' U') d' d := by
                  exact Quotient.exact (Quotient.out_eq ⟦d⟧)
                -- Apply Doset.rel_iff to extract the witnesses
                rw [Doset.rel_iff] at h_rel
                obtain ⟨h, hh, k, hk, h_eq⟩ := h_rel
                obtain ⟨γ, hγ⟩ := hh
                use γ, k, hk
                rw [← hγ] at h_eq
                exact h_eq
            obtain ⟨γ, u, hu, hd⟩ := hcoset
            have h1 : f₁.toFun d = f₁.toFun d' := by
                -- Using the left-invariance of automorphic forms.
                rw [hd, mul_assoc, f₁.left_invt γ (d' * u)]
                -- An automorphic form of level U, in the totally definite
                -- setting, is right-invariant under U by definition.
                exact congr_fun
                    (congr_arg WeightTwoAutomorphicForm.toFun (v₁.prop ⟨u, hu⟩)) d'
            -- Same as h1, TODO maybe should factor to reduce code duplication
            have h2 : f₂.toFun d = f₂.toFun d' := by
                rw [hd, mul_assoc, f₂.left_invt γ (d' * u)]
                exact congr_fun
                    (congr_arg WeightTwoAutomorphicForm.toFun (v₂.prop ⟨u, hu⟩)) d'
            rw [h1, h2]
            have : ∃ i, d' = rep (index.symm i) := by
                use index (Quot.mk _ d)
                simp only [Equiv.symm_apply_apply]
                exact rfl
            obtain ⟨i, d'_rep⟩ := this
            rw [d'_rep]
            exact congr_fun h i
        have inner_eq : f₁ = f₂ := WeightTwoAutomorphicForm.ext (f₁) (f₂) fun_eq
        apply Subtype.ext
        exact inner_eq
    exact FiniteDimensional.of_injective φ φ_injective

end TotallyDefiniteQuaternionAlgebra
