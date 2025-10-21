import Mathlib.Data.PNat.Prime
import Mathlib.Tactic.Peel
import Mathlib.Analysis.Quaternion
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import FLT.Data.QHat
import FLT.Data.Hurwitz

open scoped TensorProduct

noncomputable def HurwitzHat : Type := 𝓞 ⊗[ℤ] ZHat

namespace HurwitzHat

scoped notation "𝓞^" => HurwitzHat

noncomputable instance : Ring 𝓞^ := Algebra.TensorProduct.instRing

end HurwitzHat

noncomputable def HurwitzRat : Type := ℚ ⊗[ℤ] 𝓞

namespace HurwitzRat

scoped notation "D" => HurwitzRat

noncomputable instance : Ring D := Algebra.TensorProduct.instRing

end HurwitzRat

open scoped HurwitzRat HurwitzHat

noncomputable def HurwitzRatHat : Type := D ⊗[ℤ] ZHat

namespace HurwitzRatHat

scoped notation "D^" => HurwitzRatHat

noncomputable instance : Ring D^ := Algebra.TensorProduct.instRing

noncomputable abbrev j₁ : D →ₐ[ℤ] D^ := Algebra.TensorProduct.includeLeft
-- (Algebra.TensorProduct.assoc ℤ ℚ 𝓞 ZHat).symm.trans Algebra.TensorProduct.includeLeft

lemma injective_hRat :
    Function.Injective j₁ := sorry -- flatness

noncomputable abbrev j₂ : 𝓞^ →ₐ[ℤ] D^ :=
  ((Algebra.TensorProduct.assoc ℤ ℤ ℚ 𝓞 ZHat).symm : ℚ ⊗ 𝓞^ ≃ₐ[ℤ] D ⊗ ZHat).toAlgHom.comp
  (Algebra.TensorProduct.includeRight : 𝓞^ →ₐ[ℤ] ℚ ⊗ 𝓞^)

lemma injective_zHat :
    Function.Injective j₂ := sorry -- flatness

-- should I rearrange tensors? Not sure if D^ should be (ℚ ⊗ 𝓞) ⊗ ℤhat or ℚ ⊗ (𝓞 ⊗ Zhat)
lemma canonicalForm (z : D^) : ∃ (N : ℕ+) (z' : 𝓞^), z = j₁ ((N⁻¹ : ℚ) ⊗ₜ 1 : D) * j₂ z' := by
  sorry

lemma completed_units (z : D^ˣ) : ∃ (u : Dˣ) (v : 𝓞^ˣ), (z : D^) = j₁ u * j₂ v := sorry

end HurwitzRatHat
