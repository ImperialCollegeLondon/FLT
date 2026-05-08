/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.Quaternion -- for *notation* ℍ only!
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Is Quaternion Algebra

Material destined for Mathlib.
-/

@[expose] public section

/-- `IsQuaternionAlgebra F D` says that `D` is a quaternion algebra over the field `F`,
i.e. a four-dimensional central simple `F`-algebra. -/
class IsQuaternionAlgebra (F : Type*) [Field F] (D : Type*) [Ring D] [Algebra F D] : Prop where
  isSimpleRing : IsSimpleRing D
  isCentral : Algebra.IsCentral F D
  dim_four : Module.rank F D = 4

namespace IsQuaternionAlgebra

attribute [instance] isSimpleRing isCentral

variable (F : Type*) [Field F] (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

instance : Module.Finite F D := FiniteDimensional.of_rank_eq_nat dim_four

variable [NumberField F]

open NumberField InfinitePlace

open scoped TensorProduct Quaternion

/-- A quaternion algebra `D` over a number field `F` is totally definite if
`D ⊗[F, v] ℝ` is isomorphic to the Hamilton quaternions ℍ for all real places `v` (that is,
for all ring homomorphisms `F → ℝ`). -/
def IsTotallyDefinite : Prop := ∀ (v : InfinitePlace F) (hv : v.IsReal),
  letI : Algebra F ℝ := (embedding_of_isReal hv).toAlgebra
  Nonempty (ℝ ⊗[F] D ≃ₐ[ℝ] ℍ)

end IsQuaternionAlgebra
