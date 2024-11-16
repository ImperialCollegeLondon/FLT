import Mathlib

section defs

variable (I : Type*) (G : I → Type*) {Ht : I → Type*} (H : ∀ i, Ht i) [∀ i, SetLike (Ht i) (G i)]

def RestrictedProduct := {x : ∀ i, G i // ∀ᶠ i : I in Filter.cofinite, x i ∈ (H i : Set (G i))}

end defs

section finite_adele_example

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K]

open IsDedekindDomain DedekindDomain

example : RestrictedProduct (HeightOneSpectrum R) (fun v ↦ v.adicCompletion K)
  (fun v ↦ v.adicCompletionIntegers K) = FiniteAdeleRing R K := rfl

end finite_adele_example

variable (I : Type*) (G : I → Type*)

section monoid

variable [∀ i, Monoid (G i)] (H : ∀ i, Submonoid (G i))

instance : Monoid (RestrictedProduct I G H) where
  mul x y := ⟨fun i ↦ x.val i * y.val i, sorry⟩
  mul_assoc := sorry
  one := ⟨fun i ↦ 1, sorry⟩
  one_mul := sorry
  mul_one := sorry

end monoid

section group_problem

variable [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))

--#synth Monoid (RestrictedProduct I G H) -- fails
#synth Monoid (RestrictedProduct I G (fun i ↦ (H i).toSubmonoid)) -- works

-- instance : Group (RestrictedProduct I G H) where
--   inv x := ⟨fun i ↦ (x.val i)⁻¹, sorry⟩
--   inv_mul_cancel := sorry

-- ouch -- I might need help here.
end group_problem

-- I only need these things for: groups, rings,
-- topological groups, topological rings
section group

variable [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))

instance : Group (RestrictedProduct I G H) where
  mul x y := ⟨fun i ↦ x.val i * y.val i, sorry⟩
  mul_assoc := sorry
  one := ⟨fun i ↦ 1, sorry⟩
  one_mul := sorry
  mul_one := sorry
  inv x := ⟨fun i ↦ (x.val i)⁻¹, sorry⟩
  inv_mul_cancel := sorry

end group

section ring

variable [∀ i, Ring (G i)] (H : ∀ i, Subring (G i))

instance : AddCommGroup (RestrictedProduct I G H) where
  add x y := ⟨fun i ↦ x.val i + y.val i, sorry⟩
  add_assoc x y z := sorry
  zero := ⟨fun i ↦ 0, sorry⟩
  zero_add x := sorry
  add_zero x := sorry
  add_comm x y := sorry
  neg x := ⟨fun i ↦ -x.val i, sorry⟩
  neg_add_cancel x := sorry

instance : Ring (RestrictedProduct I G H) where
  mul x y := ⟨fun i ↦ x.val i * y.val i, sorry⟩
  mul_assoc := sorry
  zero_mul x := sorry
  mul_zero x := sorry
  left_distrib x y z := sorry
  right_distrib x y z := sorry
  one := ⟨fun i ↦ 1, sorry⟩
  one_mul := sorry
  mul_one := sorry
  zsmul := zsmulRec
  -- errorI d

end ring
/-

Group, CommRing, TopologicalSpace (careful with this one, it's not the subspace topology of ∏ᵢ Gᵢ,
it's some kind of direct limit topology), TopologicalRing, etc

-/