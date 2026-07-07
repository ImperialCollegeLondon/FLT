/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.GroupTheory.Solvable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import FLT.Slop.BrauerInduction.Main

/-!
# Brauer induction: the trivial-character / solvable-subgroup corollary

The public statement of Brauer's induction theorem for this contribution, phrased in
Mathlib's unbundled `Representation` vocabulary. The elementary form and all supporting
machinery live in the internal `Slop` directory, imported privately here so that only the
result below is exposed outside this folder.

The proof specialises the elementary theorem
`BrauerInduction.character_eq_sum_induced_linear` to the trivial one-dimensional
representation, weakens each subgroup's `IsBrauerElementary` hypothesis to `IsSolvable`
(Brauer-elementary ⇒ nilpotent ⇒ solvable), and rewrites both sides of the equation into
`Representation` vocabulary.
-/

@[expose] public section

open scoped BigOperators

universe u

namespace BrauerChallenge

theorem trivialChar_eq_sum_induced_linear_solvable
    {G : Type u} [Group G] [Finite G]
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] :
    ∃ (ι : Type) (_ : Fintype ι)
      (ns : ι → ℤ)
      (Hs : ι → Subgroup G)
      (ψs : ∀ i, Hs i →* kˣ),
      (∀ i, IsSolvable (Hs i)) ∧
        (1 : Representation k G k).character =
          ∑ i, ns i •
            (Representation.ind (Hs i).subtype
              ((algebraMap k (Module.End k k)).toMonoidHom.comp
                ((Units.coeHom k).comp (ψs i)))).character := by
  obtain ⟨ι, hι, ns, Hs, ψs, hElem, hsum⟩ :=
    BrauerInduction.character_eq_sum_induced_linear (FDRep.ofLinearChar (1 : G →* kˣ))
  refine ⟨ι, hι, ns, Hs, ψs, ?_, ?_⟩
  · -- each `Hs i` is solvable: Brauer-elementary ⇒ nilpotent ⇒ solvable
    intro i
    haveI := (hElem i).isNilpotent
    infer_instance
  · -- rewrite both sides into Mathlib's `Representation` vocabulary
    have lhs :
        (FDRep.ofLinearChar (1 : G →* kˣ)).character
          = (1 : Representation k G k).character := by
      have hρ : (FDRep.ofLinearChar (1 : G →* kˣ)).ρ = (1 : Representation k G k) := by
        apply MonoidHom.ext; intro g; apply LinearMap.ext; intro x
        change (FDRep.ofLinearChar (1 : G →* kˣ)).ρ g x = (1 : G →* Module.End k k) g x
        simp [Module.End.one_apply]
      exact congrArg Representation.character hρ
    rw [← lhs, hsum]
    exact Finset.sum_congr rfl (fun i _ => rfl)

end BrauerChallenge
