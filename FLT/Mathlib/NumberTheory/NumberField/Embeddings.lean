import Mathlib.NumberTheory.NumberField.Embeddings

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
  (v : InfinitePlace K) (w : InfinitePlace L)

theorem embedding_injective : (fun (v : InfinitePlace K) => v.embedding).Injective := by
  intro v₁ v₂ h
  dsimp at h
  rw [← mk_embedding v₁, h, mk_embedding]

theorem conjugate_embedding_injective :
    (fun (v : InfinitePlace K) => conjugate v.embedding).Injective :=
  star_injective.comp <| embedding_injective K

theorem eq_of_embedding_eq_conjugate {v₁ v₂ : InfinitePlace K}
    (h : v₁.embedding = conjugate v₂.embedding) :
    v₁ = v₂ := by
  rw [← mk_embedding v₁, h, mk_conjugate_eq, mk_embedding]

end NumberField.InfinitePlace
