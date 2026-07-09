/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# The Galois group unramified outside `S`

For a number field `F` and a finite set `S` of finite places, we define directly:
* `NumberField.IsUnramifiedOutside S M` — the property that an intermediate field `M` of `F̄/F`
* is
  **unramified outside `S`**: every finite prime `v ∉ S` of `𝒪_F` is unramified in `M`, i.e.
  for
  every maximal ideal `w` of the integral closure `𝒪_M` of `𝒪_F` in `M` lying over `v`, the
  ramification index `e(w/v) = 1`. (The integral closure is a domain even when `M/F` is infinite, so
  this makes sense for arbitrary `M`; the residue fields are finite hence perfect, so `e = 1` is
  exactly unramifiedness.)
* `NumberField.maximalUnramifiedOutside S` — the field `F_S`, the **maximal** extension of `F`
  unramified outside `S`, realized as the supremum (compositum) inside the fixed algebraic closure
  `F̄ = AlgebraicClosure F` of all intermediate fields unramified outside `S`.
* `NumberField.unramifiedOutsideGaloisGroup S` — the group `G_{F,S} = Gal(F_S/F)`, the **absolute
  Galois group of `F` unramified outside `S`**, defined as the automorphism group
  `F_S ≃ₐ[F] F_S` and carrying the Krull (profinite) topology.

It is `G_{F,S}` whose finiteness of continuous `ℤ/p`-cohomology (`Φ_p`, Hermite–Minkowski)
makes the
*global* universal deformation ring noetherian. In contrast with the full absolute Galois group
`Gal(F̄/F)` — which does **not** satisfy `Φ_p`, there being infinitely many `ℤ/p`-extensions
as the
ramification set varies — restricting the ramification to a finite `S` cuts down to a group with
the
finiteness property.

That `F_S/F` is Galois (so that `G_{F,S}` is genuinely its Galois group, a continuous quotient
of `Gal(F̄/F)`, and compact) is proved here (`NumberField.normal_maximalUnramifiedOutside`,
`NumberField.isGalois_maximalUnramifiedOutside`): `F_S` is a compositum of Galois extensions,
and separability is free in characteristic zero. The `Φ_p` finiteness is developed elsewhere.
-/

@[expose] public section

universe u

namespace NumberField

open IsDedekindDomain

variable (F : Type u) [Field F] [NumberField F]

def IsUnramifiedOutside (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (M : IntermediateField F (AlgebraicClosure F)) : Prop :=
  ∀ v : HeightOneSpectrum (RingOfIntegers F), v ∉ S →
    ∀ w : Ideal (integralClosure (RingOfIntegers F) M), w.IsMaximal →
      v.asIdeal = w.comap (algebraMap (RingOfIntegers F) (integralClosure (RingOfIntegers F) M)) →
      Ideal.ramificationIdx w (RingOfIntegers F) = 1

noncomputable def maximalUnramifiedOutside (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    IntermediateField F (AlgebraicClosure F) :=
  ⨆ (M : IntermediateField F (AlgebraicClosure F)) (_ : IsUnramifiedOutside F S M) (_ :
    IsGalois F M), M

abbrev unramifiedOutsideGaloisGroup (S : Finset (HeightOneSpectrum (RingOfIntegers F))) : Type u :=
  Gal(maximalUnramifiedOutside F S/F)

variable {F} {S : Finset (HeightOneSpectrum (RingOfIntegers F))}

/-! ### `F_S/F` is Galois

`F_S` is a compositum of subextensions that are each assumed Galois, and a compositum of
normal extensions is normal (`IntermediateField.normal_iSup`); separability is automatic in
characteristic zero. The "unramified outside `S`" predicate plays no role here — it only
selects which Galois `M` enter the compositum. -/

set_option maxHeartbeats 1600000 in
-- unifying through the `maximalUnramifiedOutside` suprema is expensive; see the section
-- comment on the cached instances below
instance normal_maximalUnramifiedOutside : Normal F ↥(maximalUnramifiedOutside F S) := by
  unfold maximalUnramifiedOutside
  have h : ∀ M : IntermediateField F (AlgebraicClosure F),
      Normal F ↥(⨆ (_ : IsUnramifiedOutside F S M) (_ : IsGalois F M), M) := fun M ↦ by
    have h1 : ∀ _ : IsUnramifiedOutside F S M, Normal F ↥(⨆ (_ : IsGalois F M), M) :=
      fun _ ↦ IntermediateField.normal_iSup (h := fun h ↦ h.to_normal)
    exact IntermediateField.normal_iSup (h := h1)
  exact IntermediateField.normal_iSup (h := h)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search walks the `maximalUnramifiedOutside` suprema; see the section comment on
-- the cached instances below
instance isGalois_maximalUnramifiedOutside : IsGalois F ↥(maximalUnramifiedOutside F S) :=
  haveI : Algebra.IsAlgebraic F ↥(maximalUnramifiedOutside F S) :=
    (normal_maximalUnramifiedOutside (F := F) (S := S)).toIsAlgebraic
  ⟨⟩

/-! ### Cached profinite instances

`G_{F,S}` is profinite under the Krull topology; deriving each of these facts walks the
`maximalUnramifiedOutside` suprema and costs ~1–2s **per search, at every use site** (measured:
19+ such searches in `REqualsT/Patching.lean` alone). Caching them here, keyed on the abbrev with
`S` generic, makes every downstream search a direct hit — including under different defeq
spellings of the bad set (`toLocalDeformationData.S` vs `badPrimes`), since `S` unifies. -/

section ProfiniteShortcuts

set_option synthInstance.maxHeartbeats 400000 in
-- instance search walks the `maximalUnramifiedOutside` suprema; see the section comment above
instance (priority := 5000) : TotallyDisconnectedSpace (unramifiedOutsideGaloisGroup F S) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search walks the `maximalUnramifiedOutside` suprema; see the section comment above.
-- Unlike the other profinite instances, compactness needs `F_S/F` to be Galois
-- (`isGalois_maximalUnramifiedOutside` above).
instance (priority := 5000) : CompactSpace (unramifiedOutsideGaloisGroup F S) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search walks the `maximalUnramifiedOutside` suprema; see the section comment above
instance (priority := 5000) : T0Space (unramifiedOutsideGaloisGroup F S) :=
  inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search walks the `maximalUnramifiedOutside` suprema; see the section comment above
instance (priority := 5000) : IsTopologicalGroup (unramifiedOutsideGaloisGroup F S) :=
  inferInstance

end ProfiniteShortcuts

end NumberField
