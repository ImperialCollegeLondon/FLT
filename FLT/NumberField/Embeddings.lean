import Mathlib.NumberTheory.NumberField.Embeddings

open scoped Classical

/-!
# Embeddings of number fields
-/

noncomputable section

namespace NumberField.InfinitePlace

variable {K : Type*} (L : Type*) [Field K] [Field L]

/--
If `L / K` are fields and `v` is an infinite place of `K`, then we say an infinite place `w`
of `L` _extends_ `v` if `w` can be constructed from a complex embedding `L →+* ℂ` whose
restriction to `K` is an associated complex embedding `K →+* ℂ` of `v`.
-/
abbrev ExtensionPlace [Algebra K L] (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v }

variable {L}

@[simp]
theorem comap_apply (w : InfinitePlace L) (f : K →+* L) (x : K) :
    w.comap f x = w (f x) := rfl

theorem comp_of_comap_eq {v : InfinitePlace K} {w : InfinitePlace L} {f : K →+* L}
    (h : w.comap f = v) (x : K) :
    w (f x) = v x := by
  simp [← h]

end InfinitePlace

namespace ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  (f : K →+* ℂ) (g : L →+* ℂ)

abbrev IsExtension := g.comp (algebraMap K L) = f

abbrev IsComplexExtension :=
  IsExtension f g ∧ ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g

namespace IsComplexExtension

theorem isExtension (h : IsComplexExtension f g) :
    IsExtension f g := h.1

theorem isReal (h : IsComplexExtension f g) :
    ComplexEmbedding.IsReal f := h.2.1

theorem not_isReal (h : IsComplexExtension f g) :
    ¬ComplexEmbedding.IsReal g := h.2.2

end IsComplexExtension

abbrev IsRealExtension := IsExtension f g ∧ ¬IsComplexExtension f g

def isExtensionEquivSum (f : K →+* ℂ) :
    { g : L →+* ℂ // IsExtension f g } ≃
      { g : L →+* ℂ // IsComplexExtension f g } ⊕
        { g : L →+* ℂ // IsRealExtension f g } := by
  apply (Equiv.sumCompl
    (fun g => ComplexEmbedding.IsReal f ∧ ¬ComplexEmbedding.IsReal g.1)).symm.trans
  apply Equiv.sumCongr
  · exact Equiv.subtypeSubtypeEquivSubtypeInter _ (fun g => _ ∧ ¬ComplexEmbedding.IsReal g)
  · apply (Equiv.subtypeSubtypeEquivSubtypeInter _
      (fun g => ¬(_ ∧ ¬ComplexEmbedding.IsReal g))).trans
    refine Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by aesop)

end NumberField.ComplexEmbedding
