/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib
import FLT.Mathlib.Algebra.IsQuaternionAlgebra -- totally definite quaternion algebras
import FLT.QuaternionAlgebra.NumberField -- rigidification

/-!
# The map from R to T

This file explains the construction of a Galois
representation Gal(F-bar/F) -> GL_2(T_m) associated
to a localisation of the Hecke algebra T, a finite Z_p-module
associated to a space of quaternionic modular forms.
-/

open IsQuaternionAlgebra NumberField

/-! Let `F` be a totally real number field. -/
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]

/-! Let `D/F` be a totally definite quaternion algebra. -/
variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]
  (hd : IsTotallyDefinite F D)

/-!
Assume `D` is unramified at all finite places. For convenience, fix once
and for all a *rigidification* `r` of `D`, which is a collection of isomorphisms
`D ⊗ Fᵥ = M₂(Fᵥ)` for all finite places v of F, compatible with the adelic structure
(i.e. inducing an isomorphism `D ⊗_F 𝔸_F^f = M₂(𝔸_F^f)`).
-/
variable (r : Rigidification F D)

/-!
Let `l > 3` be a prime unramified in `F`. The assumption `l > 3` is
made to ensure that there is no `l`-torsion in `Dˣ/Fˣ`, which will ensure
that our constructions of automorphic forms with coefficients in a `ℤₗ`-module
will commute with all base changes of coefficient modules.
-/
variable {l : ℕ} [Fact l.Prime] (hl : 3 < l)

open IsDedekindDomain

/-!
Let `R` be a finite set of finite places of `F`.
-/
variable (R : Finset (HeightOneSpectrum (𝓞 F)))

variable (v : HeightOneSpectrum (𝓞 F))

--#check 𝓞 F ⧸ v.asIdeal

--#synth CommRing (𝓞 F ⧸ v.asIdeal)

/-!
For `v ∈ R`, let `Δᵥ` be a subgroup of the units of the residue field `k(v)`.
For technical reasons, we allow `Δᵥ` to be defined for all finite places, but
we never call the function `Δᵥ` if `v ∉ R`.
-/
variable (Delta : Π v : HeightOneSpectrum (𝓞 F), Subgroup (𝓞 F ⧸ v.asIdeal)ˣ)
