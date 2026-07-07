/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.PElementaryGroup

@[expose] public section

/-!
# Brauer elementary groups

This file contains an API for Brauer elementary groups.

A group is **Brauer elementary** if it is `p`-elementary for some prime `p`.

 -/

universe u v

namespace BrauerInduction

/--
A group is **Brauer elementary** if it is `p`-elementary for some prime `p`.
-/
def IsBrauerElementary (G : Type u) [Group G] : Prop :=
  ∃ p : ℕ, p.Prime ∧ IsPElementary p G

namespace IsBrauerElementary

variable {p : ℕ}
variable {G : Type u} [Group G]
variable {G' : Type v} [Group G']

/--
A `p`-elementary group is Brauer elementary, provided `p` is prime.
-/
theorem ofIsPElementary
    (p : ℕ) [hp : Fact p.Prime]
    (hG : IsPElementary p G) :
    IsBrauerElementary G :=
  ⟨p, hp.out, hG⟩

/--
A group carrying explicit `p`-elementary structure is Brauer elementary,
provided `p` is prime.
-/
theorem ofPElementary
    (p : ℕ) [hp : Fact p.Prime]
    (eG : PElementary p G) :
    IsBrauerElementary G :=
  ofIsPElementary (p := p) ⟨eG⟩

/--
A `p`-group is Brauer elementary.
-/
theorem ofIsPGroup
    (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p G) :
    IsBrauerElementary G :=
  ofIsPElementary (p := p) (IsPElementary.ofIsPGroup (p := p) hG)

/--
Brauer elementarity is invariant under multiplicative equivalence.
-/
theorem ofMulEquiv
    (hG : IsBrauerElementary G) (φ : G ≃* G') :
    IsBrauerElementary G' := by
  rcases hG with ⟨p, hp, hpelem⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, IsPElementary.ofMulEquiv p hpelem φ⟩

/--
A subgroup of a Brauer elementary group is Brauer elementary.

This is the group-level version: if `K : Subgroup G`, then `K` is regarded as a
group in its own right.
-/
theorem ofSubgroup
    (hG : IsBrauerElementary G) (K : Subgroup G) :
    IsBrauerElementary K := by
  rcases hG with ⟨p, hp, ⟨eG⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, ⟨PElementary.ofSubgroup eG K⟩⟩

/--
Every finite cyclic group is Brauer elementary.
-/
theorem of_isCyclic
    [Finite G] (hG : IsCyclic G) :
    IsBrauerElementary G := by
  let p : ℕ := 2
  haveI : Fact p.Prime := ⟨Nat.prime_two⟩
  haveI : IsCyclic G := hG
  exact ⟨p, Nat.prime_two, IsPElementary.of_isCyclic (p := p) (G := G)⟩

/--
Every finite Brauer elementary group is nilpotent.
-/
theorem isNilpotent
    [Finite G] (hG : IsBrauerElementary G) :
    Group.IsNilpotent G := by
  rcases hG with ⟨p, hp, ⟨eG⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact eG.isNilpotent

/--
Every subgroup of a finite Brauer elementary group is nilpotent.
-/
theorem isNilpotent_subgroup
    [Finite G] (hG : IsBrauerElementary G)
    (K : Subgroup G) :
    Group.IsNilpotent K := by
  have hK : IsBrauerElementary K := ofSubgroup hG K
  exact hK.isNilpotent

end IsBrauerElementary

end BrauerInduction
