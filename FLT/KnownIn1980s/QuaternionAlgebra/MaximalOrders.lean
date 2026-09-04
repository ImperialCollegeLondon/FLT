/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.KnownIn1980s.QuaternionAlgebra.MaximalOrders.Defs
import FLT.Slop.QuaternionAlgebra.MaximalOrders

/-!
# Challenge: quaternion algebras over number fields have maximal orders

A formalization target from John Voight, *Quaternion Algebras* (GTM 288, 2021;
open-access edition at <https://quatalg.org>).

**Proposition 15.5.2** (number-field case). Let `K` be a number field with ring
of integers `𝓞 K`, and let `B` be a quaternion algebra over `K`. Then there exists
a maximal `𝓞 K`-order `O ⊆ B`, and every `𝓞 K`-order in `B` is contained in a
maximal `𝓞 K`-order.

Voight's Proposition 15.5.2 is stated over an arbitrary Dedekind domain `R` with
fraction field `F`; here we specialize to `R = 𝓞 K`, `F = K`.

## Main statements

Voight's Proposition 15.5.2 splits into its two halves:

* `exists_maximalOrder` -- a maximal `𝓞 K`-order exists.
* `exists_maximalOrder_ge` -- every `𝓞 K`-order is contained in a maximal one.
-/

@[expose] public section

open scoped NumberField Quaternion

namespace VoightMaximalOrder

variable (K : Type*) [Field K] [NumberField K] (a b : K)

/-- **Voight, *Quaternion Algebras*, Proposition 15.5.2** (number-field case),
existence half.

If `a, b ∈ Kˣ` for a number field `K`, then the quaternion algebra `ℍ[K, a, 0, b]`
contains a maximal `𝓞 K`-order. -/
theorem exists_maximalOrder (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ O : Subalgebra (𝓞 K) ℍ[K,a,0,b], IsMaximalOrder (𝓞 K) K ℍ[K,a,0,b] O :=
  _root_.slop.exists_maximalOrder K a b ha hb

/-- **Voight, *Quaternion Algebras*, Proposition 15.5.2** (number-field case),
enlargement half.

If `a, b ∈ Kˣ` for a number field `K`, then every `𝓞 K`-order in the quaternion algebra
`ℍ[K, a, 0, b]` is contained in a maximal `𝓞 K`-order. -/
theorem exists_maximalOrder_ge (ha : a ≠ 0) (hb : b ≠ 0)
    (O : Subalgebra (𝓞 K) ℍ[K,a,0,b]) (hO : IsOrder (𝓞 K) K ℍ[K,a,0,b] O) :
    ∃ O' : Subalgebra (𝓞 K) ℍ[K,a,0,b],
      IsMaximalOrder (𝓞 K) K ℍ[K,a,0,b] O' ∧ O ≤ O' :=
  _root_.slop.exists_maximalOrder_ge K a b ha hb O hO

end VoightMaximalOrder
