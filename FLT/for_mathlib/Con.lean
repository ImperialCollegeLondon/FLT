import Mathlib.GroupTheory.Congruence
import Mathlib.Algebra.BigOperators.Basic

variable {M : Type*} [AddCommMonoid M] (r : AddCon M) {ι : Type*} (s : Finset ι)

open BigOperators

namespace AddCon

lemma sum (f g : ι → M) (h : ∀ i ∈ s, r (f i) (g i)) :
    r (∑ i in s, f i) (∑ i in s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using r.refl 0
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact r.add (h _ (by simp)) <| ih fun i hi ↦ h _ (by aesop)


end AddCon
