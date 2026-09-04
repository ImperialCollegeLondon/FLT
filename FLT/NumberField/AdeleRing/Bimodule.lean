/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Mathlib.Algebra.Module.Bimodule.Basic
public import FLT.NumberField.AdeleRing

/-!
# The adele ring of `L` as an `(L, 𝔸_K)`-bimodule

For `K ⊆ L` number fields, the adele ring `𝔸 L` is simultaneously an `L`-algebra and a
right `𝔸 K`-module via the canonical (injective) ring homomorphism
`baseChange K L : 𝔸 K → 𝔸 L` followed by multiplication, and the two actions commute:
`𝔸 L` is an `(L, 𝔸 K)`-bimodule. This file records those two facts as *global*
instances,

* `RightModule (𝔸 K) (𝔸 L)` with `x <• b = x * baseChange K L b`, and
* `Bimodule L (𝔸 L) (𝔸 K)`,

together with basic compatibility lemmas. No scoped instances or local hacks are
required: both conclusions determine all their arguments, so neither instance has the
`SMul X Y → SMul (F X) (F Y)` shape that forces the `Algebra 𝔸ᶠ[K] 𝔸ᶠ[L]` instance in
`FLT.NumberField.AdeleRing` to be scoped.

## The `K = L` diamond

`RightModule (𝔸 K) (𝔸 K)` is satisfied both by `Semiring.toRightModule` (right
multiplication) and, taking `L := K`, by the instance in this file (right multiplication
through `baseChange K K`). The two are propositionally but (presumably) not
definitionally equal — the same `K = L` degeneracy that `FLT.NumberField.AdeleRing`
warns about for `Algebra (𝔸 K) (𝔸 L)`-shaped instances. The clash is not hypothetical:
it fired on the first declaration below that uses the self-action
(`baseChangeRightLinearMap`). It is arbitrated by declaring the base-change instance at
`priority := 900`, so that at `K = L` the self-action `Semiring.toRightModule` wins and
`x <• b` on `𝔸 K` always means `x * b`.

(For the record: the `K`-linear variant `Bimodule K (𝔸 L) (𝔸 K)` would need a
`Module K (𝔸 L)` instance, which mathlib does not have and this design does not need;
anyone with such an action in context can use `Bimodule.restrictScalars`.)
-/

@[expose] public section

open NumberField IsDedekindDomain

open scoped Adele Bimodule

namespace NumberField.AdeleRing

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The adele ring `𝔸 L` is a right `𝔸 K`-module: `x <• b = x * baseChange K L b`.

The priority is below `Semiring.toRightModule`'s so that at `K = L` the self-action by
right multiplication wins; see the module docstring. -/
noncomputable instance (priority := 900) : RightModule (𝔸 K) (𝔸 L) :=
  .ofRingHom (baseChange K L).toRingHom

lemma rsmul_def (x : 𝔸 L) (b : 𝔸 K) : x <• b = x * baseChange K L b :=
  rfl

/-- The adele ring `𝔸 L` is an `(L, 𝔸 K)`-bimodule: `L` acts on the left through the
`L`-algebra structure, `𝔸 K` acts on the right through `baseChange` and multiplication,
and the actions commute. -/
instance : Bimodule L (𝔸 L) (𝔸 K) :=
  Bimodule.ofRingHom (baseChange K L).toRingHom

example (l : L) (x : 𝔸 L) (b : 𝔸 K) : (l • x) <• b = l • (x <• b) :=
  smul_rsmul l x b

/-- The `(ℤ, 𝔸 K)`-bimodule structure comes for free from `Bimodule.int`. -/
example (n : ℤ) (x : 𝔸 L) (b : 𝔸 K) : (n • x) <• b = n • (x <• b) :=
  smul_rsmul n x b

lemma one_rsmul (b : 𝔸 K) : (1 : 𝔸 L) <• b = baseChange K L b :=
  one_mul _

/-- The right `𝔸 K`-action restricted to `K ⊆ 𝔸 K` agrees with the scalar action of `K`
through `L`. -/
lemma rsmul_algebraMap (x : 𝔸 L) (k : K) :
    x <• algebraMap K (𝔸 K) k = algebraMap K L k • x := by
  rw [rsmul_def, (baseChange K L).commutes, Algebra.smul_def, mul_comm]

/-- The base-change map `𝔸 K → 𝔸 L` is a morphism of right `𝔸 K`-modules, where `𝔸 K`
acts on itself by right multiplication (`Semiring.toRightModule`, which instance search
selects here thanks to the priorities discussed in the module docstring). -/
noncomputable def baseChangeRightLinearMap : (𝔸 K) →ᵣ[𝔸 K] (𝔸 L) where
  toAddMonoidHom := (baseChange K L).toRingHom.toAddMonoidHom
  map_rsmul' x b := map_mul (baseChange K L).toRingHom x b

@[simp]
lemma baseChangeRightLinearMap_apply (x : 𝔸 K) :
    baseChangeRightLinearMap K L x = baseChange K L x :=
  rfl

end NumberField.AdeleRing
