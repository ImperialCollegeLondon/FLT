import Mathlib.NumberTheory.NumberField.Embeddings

open scoped Classical

/-!
# Extensions of complex embeddings and infinite places of a number field

This file defines objects and classes for extensions of complex embeddings and extensions of
infinite places. The relationship between the two is not one-to-one. If `L / K` are fields, `w`
is an infinite place of `L` that extends the infinite place `v` over `K`, then there are
four possibilities for the relationship between their respective associated complex
embeddings `w.embedding` and `v.embedding`:
- `v` is real, `w` is complex (`w` is a ramified extension of `v`), and
  both `w.embedding` and `conjugate w.embedding` extend `v.embedding`.
- `v` and `w` are both real (i.e., `w` is an unramified real extension of `v`) and
  `w.embedding` extends `v.embedding`.
- `v` and `w` are both complex (`w` is an unramified complex extension of `v`), and
  `w.embedding` extends `v.embedding`.
- `v` and `w` are both complex, and `conjugate w.embedding` extends `v.embedding`.

## Main definitions
- `ComplexEmbedding.IsExtension f g` : predicate asserting that `g : L →+* ℂ`
  extends `f : L →+* ℂ`.
- `ComplexEmbedding.IsMixedExtension f g` : predicate determining whether `g : L →+* ℂ` extends
  `f : L →+* ℂ` and `g` is complex while `f` is real.
- `ComplexEmbedding.IsUnmixedExtension f g` : predicate determining whether `g : L →+* ℂ` extends
  `f : L →+* ℂ` and `g` is real if and only if `f` is real.
- `InfinitePlace.Extension L v` : the type of infinite places of `L` extending
  `v : InfinitePlace K` .
- `InfinitePlace.RamifiedExtension L v` : the type of infinite places of `L` that are
  ramified extensions of `v : InfinitePlace K`.
- `InfinitePlace.UnramifiedExtension L v` : the type of infinite places of `L` that are
  unramified extensions of `v : InfinitePlace K`.
- `InfinitePlace.Real` (resp. `InfinitePlace.Complex`) : class version of `InfinitePlace.IsReal`
  (resp. `InfinitePlace.IsComplex`).
- `InfinitePlace.Extension.IsLift L v w`: class encoding the property that `w.embedding` extends
  `v.embedding`.
- `InfinitePlace.Extension.IsConjugateLift L v w` : class encoding the property that
  `conjugate w.embedding` extends `v.embedding`.
-/

noncomputable section

namespace NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  (f : K →+* ℂ) (g : L →+* ℂ)

omit [Algebra K L] in
@[simp]
theorem conjugate_comp (σ : K →+* L) : (conjugate g).comp σ = conjugate (g.comp σ) := rfl

/--
If `L/K` and `f : K →+* ℂ`, `g : L →+* ℂ`, then we say `g` is an extension of `f` if
`g` restricted to `K` is `f`.

This is the complex embedding analogue of `InfinitePlace.Extension`.
-/
abbrev IsExtension := g.comp (algebraMap K L) = f

variable {f g} in
theorem IsExtension.not_isExtension_conjugate (h : IsExtension f g)
    (hf : ¬ComplexEmbedding.IsReal f) :
    ¬IsExtension f (conjugate g) := by
  simp_all [RingHom.ext_iff, ComplexEmbedding.isReal_iff]

variable {f g} in
theorem IsExtension.ne {r : L →+* ℂ} (hg : IsExtension f g) (hr : ¬IsExtension f r) :
    g ≠ r := by
  simp_all only [← hg, RingHom.ext_iff, RingHom.coe_comp, Function.comp_apply, not_forall,
    ne_eq]
  let ⟨x, hx⟩ := hr
  exact ⟨algebraMap K L x, by aesop⟩

/--
If `L/K` and `f : K →+* ℂ`, `g : L →+* ℂ`, then `g` is a _mixed extension_ of `f` if the
image of `f` is real while the image of `g` is complex.

This is the complex embedding analogue of `InfinitePlace.RamifiedExtension`.
-/
abbrev IsMixedExtension :=
  IsExtension f g ∧ ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g

theorem not_isReal_of_not_isReal {f : K →+* ℂ} {g : L →+* ℂ} (h : IsExtension f g)
    (hf : ¬ComplexEmbedding.IsReal f) :
    ¬ComplexEmbedding.IsReal g :=
  mt (IsReal.comp _) (h ▸ hf)

namespace IsMixedExtension

theorem isExtension (h : IsMixedExtension f g) :
    IsExtension f g := h.1

theorem isReal (h : IsMixedExtension f g) :
    ComplexEmbedding.IsReal f := h.2.1

theorem not_isReal (h : IsMixedExtension f g) :
    ¬ComplexEmbedding.IsReal g := h.2.2

end IsMixedExtension

/--
If `L/K` and `f : K →+* ℂ`, `g : L →+* ℂ`, then `g` is an _unmixed extension_ of `f` if `g` is an
extension of `f` but is not a mixed extension. In other words, the image of `f` is real
if and only if the image of `g` is real.

This is the complex embedding analogue of `InfinitePlace.UnramifiedExtension`.
-/
abbrev IsUnmixedExtension := IsExtension f g ∧ ¬IsMixedExtension f g

variable {f g} in
theorem IsUnmixedExtension.isReal_of_isReal (h : IsUnmixedExtension f g)
    (hf : ComplexEmbedding.IsReal f) :
    ComplexEmbedding.IsReal g := by
  simp only [IsUnmixedExtension, not_and, not_not] at h
  exact h.2 h.1 hf

/--
The extensions `g : L →+* ℂ` of `f : K →+* ℂ` are the direct sum of the mixed and the unmixed
extensions.
-/
def isExtensionEquivSum (f : K →+* ℂ) :
    { g : L →+* ℂ // IsExtension f g } ≃
      { g : L →+* ℂ // IsMixedExtension f g } ⊕ { g : L →+* ℂ // IsUnmixedExtension f g } :=
  (Equiv.sumCompl
    (fun g => ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g.1)).symm.trans <|
    Equiv.sumCongr
      (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun g => _ ∧ ¬ComplexEmbedding.IsReal g))
      ((Equiv.subtypeSubtypeEquivSubtypeInter _
        (fun g => ¬(_ ∧ ¬ComplexEmbedding.IsReal g))).trans
        (Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by aesop)))

end NumberField.ComplexEmbedding

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] (v : InfinitePlace K) (w : InfinitePlace L)

@[simp]
theorem comap_apply (f : K →+* L) (x : K) :
    w.comap f x = w (f x) := rfl

variable {v w} in
theorem comp_of_comap_eq {f : K →+* L} (h : w.comap f = v) (x : K) :
    w (f x) = v x := by
  simp [← h]

/-- Class encoding the fact that an infinite place is real. -/
class Real where
  isReal' : v.IsReal

theorem Real.isReal [v.Real] : v.IsReal := Real.isReal'

/-- Class encoding the fact that an infinite place is complex. -/
class Complex where
  isComplex' : v.IsComplex

theorem Complex.isComplex [v.Complex] : v.IsComplex := Complex.isComplex'

theorem not_real_iff_complex : ¬v.Real ↔ v.Complex := by
  refine ⟨fun h => ⟨?_⟩, fun ⟨hc⟩ ⟨hr⟩ => not_isReal_iff_isComplex.2 hc hr⟩
  rw [← not_isReal_iff_isComplex]
  contrapose! h
  exact ⟨h⟩

variable [Algebra K L]

variable (K) in
/-- An infinite place `w` of `L` is ramified over `K` if it is not unramified. In other words,
`w` is complex while the restriction `w.comap (algebraMap K L)` to `K` is real. -/
abbrev IsRamified := ¬w.IsUnramified K

variable {w} in
theorem isRamified_iff : w.IsRamified K ↔ w.IsComplex ∧ (w.comap (algebraMap K L)).IsReal :=
  not_isUnramified_iff

variable {w} in
theorem IsRamified.ne_conjugate {w₁ w₂ : InfinitePlace L} (h₂ : IsRamified K w₂) :
    w₁.embedding ≠ conjugate w₂.embedding := by
  rw [ne_eq]
  by_cases h : w₁ = w₂
  · rw [h]
    rw [isRamified_iff, isComplex_iff, ComplexEmbedding.isReal_iff] at h₂
    exact Ne.symm h₂.1
  · contrapose! h
    rw [← mk_embedding w₁, h, mk_conjugate_eq, mk_embedding]

variable (L) in
/--
If `L / K` are fields and `v` is an infinite place of `K`, then we say an infinite place `w`
of `L` _extends_ `v` if `w` can be constructed from a complex embedding `L →+* ℂ` whose
restriction to `K` is an associated complex embedding `K →+* ℂ` of `v`.
-/
abbrev Extension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v }

namespace Extension

variable {v : InfinitePlace K} (w : v.Extension L)

theorem isComplex_of_isComplex (hv : v.IsComplex) :
    w.1.IsComplex := by
  rw [isComplex_iff, ComplexEmbedding.isReal_iff, RingHom.ext_iff, not_forall] at hv ⊢
  let ⟨x, hx⟩ := hv
  use algebraMap K L x
  rw [← w.2, ← mk_embedding w.1, comap_mk] at hx
  cases embedding_mk_eq (w.1.embedding.comp (algebraMap K L)) with
  | inl hl => simp_all
  | inr hr => aesop

theorem isReal_base (hw : w.1.IsReal) :
    v.IsReal := by
  simp_all only [← not_isComplex_iff_isReal]
  exact mt w.isComplex_of_isComplex hw

instance [Algebra K L] {v : InfinitePlace K} {w : v.Extension L}
    [v.Complex] : w.1.Complex := ⟨w.isComplex_of_isComplex (Complex.isComplex v)⟩

theorem mk_embedding : mk (w.1.embedding.comp (algebraMap K L)) = v := by
  rw [← comap_mk, w.1.mk_embedding, w.2]

theorem isExtension_or_isExtension_conjugate :
    IsExtension v.embedding w.1.embedding ∨ IsExtension v.embedding (conjugate w.1.embedding) := by
  cases embedding_mk_eq (w.1.embedding.comp (algebraMap K L)) with
  | inl hl =>
    convert Or.inl <| hl ▸ congrArg InfinitePlace.embedding w.mk_embedding
  | inr hr =>
    convert Or.inr <| hr ▸ congrArg InfinitePlace.embedding w.mk_embedding

theorem isExtension_conjugate_of_not_isExtension (h : ¬IsExtension v.embedding w.1.embedding) :
    IsExtension v.embedding (conjugate w.1.embedding) :=
  w.isExtension_or_isExtension_conjugate.resolve_left h

variable (L)

variable (v : InfinitePlace K) (w : v.Extension L)

/--
If `w` is an infinite place of `L` lying above the infinite place `v` of
`K`, then there are two possibilities:
- `w.embedding` extends `v.embedding`.
- `conjugate w.embedding` extends `v.embedding`.

`IsLift w` encodes the first case.
-/
class IsLift where
  isExtension' : IsExtension v.embedding w.1.embedding

theorem IsLift.isExtension [w.IsLift L v] : IsExtension v.embedding w.1.embedding :=
  IsLift.isExtension'

/--
If `w` is an infinite place of `L` lying above the infinite place `v` of
`K`, then there are two possibilities:
- `w.embedding` extends `v.embedding`.
- `conjugate w.embedding` extends `v.embedding`.

`IsConjugateLift w` encodes the second case.
-/
class IsConjugateLift where
  isExtension' : IsExtension v.embedding (conjugate w.1.embedding)

theorem IsConjugateLift.isExtension [w.IsConjugateLift L v] :
    IsExtension v.embedding (conjugate w.1.embedding) := IsConjugateLift.isExtension'

theorem isLift_or_isConjugateLift (v : InfinitePlace K) (w : v.Extension L) :
    w.IsLift L v ∨ w.IsConjugateLift L v := by
  cases isExtension_or_isExtension_conjugate w with
  | inl hl => exact Or.inl ⟨hl⟩
  | inr hr => exact Or.inr ⟨hr⟩

end Extension

variable (L)

/-- For a given infinite place `v` of `K`, `RamifiedExtension L v` are all the infinite places
of `L / K` that extend `v` and are ramified over `K`. -/
abbrev RamifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsRamified K }

/-- For a given infinite place `v` of `K`, `UnramifiedExtension L v` are all the infinite places
of `L / K` that extend `v` and are unramified over `K`. -/
abbrev UnramifiedExtension (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsUnramified K }

variable {L v}

/-- Construct a `v.RamifiedExtension L` term from a `w : v.Extension L` such that
`w.1.IsRamified K`. -/
def Extension.toRamifiedExtension {w : v.Extension L} (h : w.1.IsRamified K) :
    v.RamifiedExtension L := ⟨w.1, ⟨w.2, h⟩⟩

/-- Construct a `v.UnramifiedExtension L` term from a `w : v.Extension L` such that
`w.1.IsUnramified K`. -/
def Extension.toUnramifiedExtension {w : v.Extension L} (h : w.1.IsUnramified K) :
    v.UnramifiedExtension L := ⟨w.1, ⟨w.2, h⟩⟩

namespace RamifiedExtension

theorem comap_eq (w : v.RamifiedExtension L) : w.1.comap (algebraMap K L) = v := w.2.1

theorem isRamified (w : v.RamifiedExtension L) : w.1.IsRamified K := w.2.2

theorem isReal_comap (w : v.RamifiedExtension L) : (w.1.comap (algebraMap K L)).IsReal :=
  (isRamified_iff.1 w.isRamified).2

instance : Coe (v.RamifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.2.1⟩

theorem isReal (w : v.RamifiedExtension L) : v.IsReal :=
  w.comap_eq ▸ w.isReal_comap

theorem isComplex (w : v.RamifiedExtension L) :
    (w.1 : InfinitePlace L).IsComplex :=
  (isRamified_iff.1 w.isRamified).1

instance (w : v.RamifiedExtension L) : w.1.Complex := ⟨w.isComplex⟩

end RamifiedExtension

namespace UnramifiedExtension

theorem comap_eq (w : UnramifiedExtension L v) : w.1.comap (algebraMap K L) = v := w.2.1

theorem isUnramified (w : UnramifiedExtension L v) : w.1.IsUnramified K := w.2.2

instance : Coe (v.UnramifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.comap_eq⟩

end UnramifiedExtension

end NumberField.InfinitePlace
