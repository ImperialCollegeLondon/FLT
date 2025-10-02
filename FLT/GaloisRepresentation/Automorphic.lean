/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Kevin Buzzard
-/
import Mathlib
import FLT

/-!
# Automorphic Galois representations

For our proof of Fermat's Last Theorem, the following definition is the most convenient.

We say that a 2-dimensional $p$-adic or a mod $p$ Galois representation of the absolute
Galois of a totally real field number field $F$ is *automorphic* if there exists a totally
definite quaternion algebra $D/F$ unramified at all finite places, a squarefree ideal $n$
of the integers of $F$, and an automorphic form of level $U_1(n)$ (matrices congruent
to $(a *;0 a)$ mod $n$) and weight 2 for $D$
such that the Galois representation is associated to the form by the construction of
Carayol, Taylor et al.

## Notes

Several things here are non-standard. We demand that the quaternion algebra is unramified
everywhere because this is the only case that we need. We stick to weight 2 because this is
the only case that we need. The level is also non-standard: the automorphic forms it
catches are principal series`π(χ₁, χ₂)` with `χᵢ` tame and `χ₁χ₂` unramified, and
also Steinberg representations.

-/

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsLocalRing A]

open scoped TensorProduct

open IsDedekindDomain NumberField TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

-- /-- TODO docstring -/
def GaloisRep.IsModular {F : Type*} (D : Type*) (p : ℕ) [NeZero p] [Field F] [NumberField F]
    [IsTotallyReal F] {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V]
    (𝒪 : Type*) [CommRing 𝒪] [Algebra 𝒪 A]
    [Module.Free A V] (_hV : Module.finrank A V = 2) (ρ : GaloisRep F A V) [Ring D] [Algebra F D]
    [IsQuaternionAlgebra F D] (r : IsQuaternionAlgebra.NumberField.Rigidification F D)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∃ (π : HeckeAlgebra F D r S 𝒪 →ₐ[𝒪] A),
    ∀ (v : HeightOneSpectrum (𝓞 F)) (_hvp : ↑p ∉ v.1) (hvS : v ∉ S),
      ρ.IsUnramifiedAt v ∧ (ρ.toLocal v (Frob v)).det = v.1.absNorm
      ∧ LinearMap.trace A V (ρ.toLocal v (Frob v)) =
        π (HeckeAlgebra.T D r 𝒪 v hvS)
