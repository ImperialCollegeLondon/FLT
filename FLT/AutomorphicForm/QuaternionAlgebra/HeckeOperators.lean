import Mathlib -- TODO remove all these
/-

# Hecke operators

We give an abstract exposition of the theory of Hecke operators

## The mathematics

The set-up: a group G acts on additive group A, g ∈ G,
and U,V are subgroups of G. We impose the finiteness hypothesis
that the subgroup g⁻¹Ug ∩ V of V has finite index. Under this
hypothesis we define a Hecke operator [UgV], an additive group
homorphism from A^V to A^U.

Before we give the definition, let us observe that by the second
isomorphism theorem, our finiteness hypothesis tells us that
g⁻¹UgV is a finite union of left cosets hᵢV of V, and
hence the double coset UgV is a finite union of single cosets gᵢV.

The definition of the Hecke operator is as follows. Write UgV as a
finite disjoint union gᵢV.
If a ∈ A^V then we define `[UgV]a := ∑ᵢ gᵢ•a`. Note that replacing
the choice of gᵢ with another element g'ᵢ := gᵢv will not change gᵢ•a
as a ∈ A^v, so the sum is a well-defined element of A. Finally
we observe that it's in A^U because if u ∈ U then left multiplication
by u is a permutation of the cosets gᵢV.

Note that if G is a topological group and U, V are compact open
subgroups of G, then our hypothesis is automatically satisfied
for all g ∈ G, because g⁻¹Ug ∩ V is open in compact V and hence
has finite index.

-/
variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [MulAction G A] (g : G) (U V : Subgroup G)
