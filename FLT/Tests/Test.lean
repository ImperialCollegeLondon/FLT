/-
Scratch file collecting the experiments from a chat investigating why typeclass
synthesis for `AddCommMonoid (Πʳ v, [(w : Extension B v) → adicCompletion L w.1, …])`
in `FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean` was burning ~54M heartbeats.

The investigation tracked down a `=?=` printed in the synth trace, of the form
`Valued.toUniformSpace … =?= Valued.toUniformSpace …`, to a diamond on
`Preorder (Multiplicative ℤ)` sitting inside the
`LinearOrderedCommGroupWithZero (WithZero (Multiplicative ℤ))` instance.

Examples below, in increasing complexity:
  (1) `IsOrderedMonoid` is `Prop`, so proof irrelevance applies.
  (2) Two proofs of `IsOrderedMonoid (Multiplicative ℤ)` from different sources
      have *different (defeq) types* because of a `Preorder` diamond.
  (3) Two `WithZero.instLinearOrderedCommGroupWithZero` instances that differ
      only in their `IsOrderedMonoid` argument are still defeq by `rfl`.
  (4) The full LHS = RHS literally pasted from the failing synth trace, with
      named instances, also closes by `rfl`.

Conclusion: the diamond is real but the kernel sees through it at full
transparency. The `set_option backward.isDefEq.respectTransparency false`
active at the failing site is what turns the latent diamond into the visible
`=?=` and the heartbeat blowup.

***

⏺ Clean build, no errors or warnings. FLT/Test.lean is ready with the four examples from our investigation:

  1. #check @IsOrderedMonoid and a proof-irrelevance check confirming it's a Prop.
  2. Two #check calls with pp.all showing the diamond — _proof_1's type goes through Multiplicative ℤ's own lattice, while Multiplicative.isOrderedMonoid's type goes through ℤ's
  ConditionallyCompleteLinearOrder and then bounces back via Multiplicative.preorder.
  3. A small rfl between two WithZero.instLinearOrderedCommGroupWithZero instances that differ only in their IsOrderedMonoid argument.
  4. The full Valued.toUniformSpace …  =  Valued.toUniformSpace … literally transcribed from the failing synth trace, closed by rfl.

***
-/

import FLT.DedekindDomain.Completion.BaseChange
import FLT.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module
import FLT.Mathlib.Topology.Algebra.Algebra.Hom
import FLT.Mathlib.LinearAlgebra.Pi
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Flat.TorsionFree
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Algebra.Order.Algebra
import Mathlib.RingTheory.SimpleRing.Principal

-- Investigating `_proof_1` is the whole point of this file.
set_option linter.auxLemma false

namespace FLTTest

open IsDedekindDomain HeightOneSpectrum adicCompletion Extension

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

/-! ### (1) `IsOrderedMonoid` is a `Prop` -/

#check @IsOrderedMonoid
-- IsOrderedMonoid : (α : Type u_1) → [CommMonoid α] → [Preorder α] → Prop

example (α : Type) [CommMonoid α] [Preorder α] (h₁ h₂ : IsOrderedMonoid α) : h₁ = h₂ := rfl

/-! ### (2) The diamond made visible

Both terms below inhabit `IsOrderedMonoid (Multiplicative ℤ)`, but their *types*
(printed in full) differ in the implicit `Preorder (Multiplicative ℤ)` argument:

* `_proof_1` carries a `Preorder` built by
  `Multiplicative.linearOrder ℤ → instDistribLatticeOfLinearOrder → … →
   PartialOrder.toPreorder` **on `Multiplicative ℤ`**.
* `Multiplicative.isOrderedMonoid` carries a `Preorder` built from
  `Int.instLatticeInt` **on `ℤ`** and then transported via `Multiplicative.preorder`. -/

set_option pp.all true in
#check @IsDedekindDomain.HeightOneSpectrum.valuation._proof_1

set_option pp.all true in
#check (@Multiplicative.isOrderedMonoid ℤ _ _ _ : IsOrderedMonoid (Multiplicative ℤ))

/-! ### (3) Simple instance equality

Two `LinearOrderedCommGroupWithZero (WithZero (Multiplicative ℤ))` instances that
differ only in their `IsOrderedMonoid` argument — the kernel closes this by
`rfl` (it sees through `Multiplicative.preorder = id`). -/

example :
    (WithZero.instLinearOrderedCommGroupWithZero :
        LinearOrderedCommGroupWithZero (WithZero (Multiplicative ℤ))) =
    @WithZero.instLinearOrderedCommGroupWithZero (Multiplicative ℤ) _ _
      (@Multiplicative.isOrderedMonoid ℤ _ _ _) := by with_reducible_and_instances rfl

/-! ### (4) The full term from the failing synth trace

This is the literal `=?=` printed by `pp.all`, with `inst✝N` replaced by the
section variables and `_proof_1` written by name. The only differences between
LHS and RHS are the `IsOrderedMonoid` arguments inside three of the four
`WithZero.instLinearOrderedCommGroupWithZero` occurrences. -/

set_option trace.profiler.useHeartbeats true in
set_option trace.profiler true in
example
    (v : HeightOneSpectrum A)
    (i : { w : HeightOneSpectrum B // w.under A = v }) :
    @Valued.toUniformSpace
        (@WithVal L (WithZero (Multiplicative ℤ))
          (@WithZero.instLinearOrderedCommGroupWithZero (Multiplicative ℤ)
            (@Multiplicative.commGroup ℤ Int.instAddCommGroup)
            (@Multiplicative.linearOrder ℤ Int.instLinearOrder)
            IsDedekindDomain.HeightOneSpectrum.valuation._proof_1)
          (@DivisionRing.toRing L (@Field.toDivisionRing L inferInstance))
          (@HeightOneSpectrum.valuation B inferInstance inferInstance L
            inferInstance inferInstance inferInstance i.val))
        (@WithVal.instRing L (WithZero (Multiplicative ℤ))
          (@WithZero.instLinearOrderedCommGroupWithZero (Multiplicative ℤ)
            (@Multiplicative.commGroup ℤ Int.instAddCommGroup)
            (@Multiplicative.linearOrder ℤ Int.instLinearOrder)
            IsDedekindDomain.HeightOneSpectrum.valuation._proof_1)
          (@DivisionRing.toRing L (@Field.toDivisionRing L inferInstance))
          (@HeightOneSpectrum.valuation B inferInstance inferInstance L
            inferInstance inferInstance inferInstance i.val))
        (WithZero (Multiplicative ℤ))
        (@WithZero.instLinearOrderedCommGroupWithZero (Multiplicative ℤ)
          (@Multiplicative.commGroup ℤ Int.instAddCommGroup)
          (@Multiplicative.linearOrder ℤ Int.instLinearOrder)
          IsDedekindDomain.HeightOneSpectrum.valuation._proof_1)
        (@WithVal.instValued L (WithZero (Multiplicative ℤ))
          (@WithZero.instLinearOrderedCommGroupWithZero (Multiplicative ℤ)
            (@Multiplicative.commGroup ℤ Int.instAddCommGroup)
            (@Multiplicative.linearOrder ℤ Int.instLinearOrder)
            IsDedekindDomain.HeightOneSpectrum.valuation._proof_1)
          (@DivisionRing.toRing L (@Field.toDivisionRing L inferInstance))
          (@HeightOneSpectrum.valuation B inferInstance inferInstance L
            inferInstance inferInstance inferInstance i.val))
    =
    @Valued.toUniformSpace
        (@WithVal L (WithZero (Multiplicative ℤ))
          (@WithZero.instLinearOrderedCommGroupWithZero (Multiplicative ℤ)
            (@Multiplicative.commGroup ℤ Int.instAddCommGroup)
            (@Multiplicative.linearOrder ℤ Int.instLinearOrder)
            IsDedekindDomain.HeightOneSpectrum.valuation._proof_1)
          (@DivisionRing.toRing L (@Field.toDivisionRing L inferInstance))
          (@HeightOneSpectrum.valuation B inferInstance inferInstance L
            inferInstance inferInstance inferInstance i.val))
        (@WithVal.instRing L (WithZero (Multiplicative ℤ))
          (@WithZero.instLinearOrderedCommGroupWithZero (Multiplicative ℤ)
            (@Multiplicative.commGroup ℤ Int.instAddCommGroup)
            (@Multiplicative.linearOrder ℤ Int.instLinearOrder)
            (@Multiplicative.isOrderedMonoid ℤ Int.instAddCommMonoid
              (@PartialOrder.toPreorder (Multiplicative ℤ)
                (@SemilatticeInf.toPartialOrder (Multiplicative ℤ)
                  (@Lattice.toSemilatticeInf (Multiplicative ℤ)
                    (@DistribLattice.toLattice (Multiplicative ℤ)
                      (@instDistribLatticeOfLinearOrder (Multiplicative ℤ)
                        (@Multiplicative.linearOrder ℤ Int.instLinearOrder))))))
              Int.instIsOrderedAddMonoid))
          (@DivisionRing.toRing L (@Field.toDivisionRing L inferInstance))
          (@HeightOneSpectrum.valuation B inferInstance inferInstance L
            inferInstance inferInstance inferInstance i.val))
        (WithZero (Multiplicative ℤ))
        (@WithZero.instLinearOrderedCommGroupWithZero (Multiplicative ℤ)
          (@Multiplicative.commGroup ℤ Int.instAddCommGroup)
          (@Multiplicative.linearOrder ℤ Int.instLinearOrder)
          (@Multiplicative.isOrderedMonoid ℤ Int.instAddCommMonoid
            (@PartialOrder.toPreorder (Multiplicative ℤ)
              (@SemilatticeInf.toPartialOrder (Multiplicative ℤ)
                (@Lattice.toSemilatticeInf (Multiplicative ℤ)
                  (@DistribLattice.toLattice (Multiplicative ℤ)
                    (@instDistribLatticeOfLinearOrder (Multiplicative ℤ)
                      (@Multiplicative.linearOrder ℤ Int.instLinearOrder))))))
            Int.instIsOrderedAddMonoid))
        (@WithVal.instValued L (WithZero (Multiplicative ℤ))
          (@WithZero.instLinearOrderedCommGroupWithZero (Multiplicative ℤ)
            (@Multiplicative.commGroup ℤ Int.instAddCommGroup)
            (@Multiplicative.linearOrder ℤ Int.instLinearOrder)
            (@Multiplicative.isOrderedMonoid ℤ Int.instAddCommMonoid
              (@PartialOrder.toPreorder (Multiplicative ℤ)
                (@SemilatticeInf.toPartialOrder (Multiplicative ℤ)
                  (@Lattice.toSemilatticeInf (Multiplicative ℤ)
                    (@DistribLattice.toLattice (Multiplicative ℤ)
                      (@instDistribLatticeOfLinearOrder (Multiplicative ℤ)
                        (@Multiplicative.linearOrder ℤ Int.instLinearOrder))))))
              Int.instIsOrderedAddMonoid))
          (@DivisionRing.toRing L (@Field.toDivisionRing L inferInstance))
          (@HeightOneSpectrum.valuation B inferInstance inferInstance L
            inferInstance inferInstance inferInstance i.val))
    := by with_reducible_and_instances rfl

end FLTTest
