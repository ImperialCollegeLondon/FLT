import Mathlib.NumberTheory.NumberField.Embeddings

/-!
# Embeddings of number fields
-/

namespace NumberField.InfinitePlace

variable {K : Type*} (L : Type*) [Field K] [Field L] [Algebra K L]

/--
If `L / K` are fields and `v` is an infinite place of `K`, then we say an infinite place `w`
of `L` _extends_ `v` if `w` can be constructed from a complex embedding `L →+* ℂ` whose
restriction to `K` is an associated complex embedding `K →+* ℂ` of `v`. -/
abbrev ExtensionPlace (v : InfinitePlace K) :=
  { w : InfinitePlace L // w.comap (algebraMap K L) = v }

namespace ExtensionPlace

variable {L}

theorem abs_comp {v : InfinitePlace K} (wv : v.ExtensionPlace L) (x : K) :
    wv.1 (algebraMap K L x) = v x := by
  simp_rw [← wv.2]; rfl

end NumberField.InfinitePlace.ExtensionPlace
