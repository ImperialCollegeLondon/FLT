/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.Representation

@[expose] public section

/-!
# Invariants of the internal Hom representation

This file identifies invariant vectors of the representation
`Representation.linHom X.ρ Y.ρ` with morphisms `X ⟶ Y` in `Rep k G`.
-/

namespace Rep

open CategoryTheory

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The invariants of `linHom X.ρ Y.ρ` are representation homomorphisms `X ⟶ Y`. -/
noncomputable def linHomInvariantsEquivHom
    (X Y : Rep k G) :
    (Representation.linHom X.ρ Y.ρ).invariants ≃ₗ[k] (X ⟶ Y) where
  toFun f :=
    Rep.ofHom
      ⟨f.1, by
        intro g
        exact
          (Representation.linHom.mem_invariants_iff_comm f.1 g).1 (f.2 g)⟩
  invFun f :=
    ⟨f.hom.toLinearMap, by
      intro g
      exact
        (Representation.linHom.mem_invariants_iff_comm f.hom.toLinearMap g).2
          ((Rep.Hom.hom f).isIntertwining' g)
      ⟩
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl
  left_inv := by
    intro f
    ext x
    rfl
  right_inv := by
    intro f
    apply Rep.Hom.ext
    apply Representation.IntertwiningMap.ext
    ext x
    rfl

end Rep
