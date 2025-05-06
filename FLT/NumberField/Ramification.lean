import Mathlib.NumberTheory.NumberField.Embeddings

import Mathlib.NumberTheory.NumberField.Embeddings
import FLT.NumberField.Embeddings

open scoped Classical

/-!
# Embeddings of number fields
-/

noncomputable section

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable (K : Type*) {L : Type*} [Field K] [Field L]
variable [Algebra K L] (v : InfinitePlace K) (w : InfinitePlace L)

abbrev IsRamified := ¬w.IsUnramified K

variable {K} (L)

namespace IsRamified

def sumEquivIsComplexExtension :
    let 𝓟 := { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsRamified K }
    let 𝓔 := { ψ : L →+* ℂ // IsComplexExtension v.embedding ψ }
    𝓟 ⊕ 𝓟 ≃ 𝓔 :=
  sorry

theorem two_mul_card_eq [NumberField L] :
    let 𝓟 := { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsRamified K }
    let 𝓔 := { ψ : L →+* ℂ // IsComplexExtension v.embedding ψ }
    2 * Fintype.card 𝓟 = Fintype.card 𝓔 := by
  simp [← Fintype.card_eq.2 ⟨sumEquivIsComplexExtension L v⟩]
  ring

end IsRamified

namespace IsUnramified

def equivIsRealExtension :
    let 𝓟 := { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsUnramified K }
    let 𝓔 := { ψ : L →+* ℂ // IsRealExtension v.embedding ψ }
    𝓟 ≃ 𝓔 :=
  sorry

theorem card_eq [NumberField L] :
    let 𝓟 := { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsUnramified K }
    let 𝓔 := { ψ : L →+* ℂ // IsRealExtension v.embedding ψ }
    Fintype.card 𝓟 = Fintype.card 𝓔 := by
  simp [← Fintype.card_eq.2 ⟨equivIsRealExtension L v⟩]

end IsUnramified

variable (K) {L}

abbrev ramificationIdx := if w.IsUnramified K then 1 else 2

variable {w}

theorem ramificationIdx_eq_one (h : w.IsUnramified K) :
    ramificationIdx K w = 1 := by
  rw [ramificationIdx, if_pos h]

theorem ramificationIdx_eq_two (h : w.IsRamified K) :
    ramificationIdx K w = 2 := by
  rw [ramificationIdx, if_neg h]

namespace ExtensionPlace

variable {K} (L)

theorem card_isUnramified_add_two_mul_card_isRamified [NumberField K] [NumberField L] :
    let 𝓟ᵤ := { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsUnramified K }
    let 𝓟ᵣ := { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsRamified K }
    Fintype.card 𝓟ᵤ + 2 * Fintype.card 𝓟ᵣ = Module.finrank K L := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  rw [← AlgHom.card K L ℂ]
  have (φ : L →ₐ[K] ℂ) : φ.toRingHom.comp (algebraMap K L) = v.embedding := by
    have := funext_iff.2 φ.commutes'
    rw [RingHom.algebraMap_toAlgebra] at this
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.commutes,
      DFunLike.coe_fn_eq] at this
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]
  let g : (L →ₐ[K] ℂ) → { ψ : L →+* ℂ // IsExtension v.embedding ψ } :=
    fun φ => ⟨φ.toRingHom, this φ⟩
  have hg_inj : g.Injective := by
    intro φ₁ φ₂ h
    simp only [AlgHom.toRingHom_eq_coe, Subtype.mk.injEq, g] at h
    exact AlgHom.coe_ringHom_injective h
  have {σ : L →+* ℂ} (h : σ.comp (algebraMap K L) = v.embedding) :
      ∀ (r : K), σ.toFun (algebraMap K L r) = algebraMap K ℂ r := by
    intro k
    rw [RingHom.algebraMap_toAlgebra, ← h]
    rfl
  have hg_surj : g.Surjective := by
    intro ⟨σ, h⟩
    use {
      __ := σ
      commutes' := this h
    }
  have : (L →ₐ[K] ℂ) ≃ { ψ : L →+* ℂ // IsExtension v.embedding ψ } :=
    Equiv.ofBijective _ ⟨hg_inj, hg_surj⟩
  rw [Fintype.card_eq.2 ⟨this⟩]
  rw [Fintype.card_eq.2 ⟨isExtensionEquivSum v.embedding⟩]
  rw [Fintype.card_sum]
  rw [Fintype.card_eq.2 ⟨(IsRamified.sumEquivIsComplexExtension L v).symm⟩]
  rw [Fintype.card_sum]
  rw [Fintype.card_eq.2 ⟨(IsUnramified.equivIsRealExtension L v).symm⟩]
  ring

theorem sum_ramificationIdx_eq [NumberField K] [NumberField L] :
    ∑ w : v.ExtensionPlace L, w.1.ramificationIdx K = Module.finrank K L := by
  let 𝓟ᵤ := { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsUnramified K }
  let 𝓟ᵣ := { w : InfinitePlace L // w.comap (algebraMap K L) = v ∧ w.IsRamified K }
  let e : v.ExtensionPlace L ≃ 𝓟ᵤ ⊕ 𝓟ᵣ :=
    (Equiv.sumCompl _).symm.trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).sumCongr
        (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun w => ¬IsUnramified K w))
  rw [Fintype.sum_equiv e _ ((fun w => w.1.ramificationIdx K) ∘ e.symm)
    (fun _ => by simp only [Function.comp_apply, Equiv.symm_apply_apply])]
  simp only [Function.comp_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Fintype.sum_sum_type, Sum.map_inl, Equiv.sumCompl_apply_inl, e,
    Equiv.subtypeSubtypeEquivSubtypeInter_symm_apply_coe_coe, Sum.map_inr, Equiv.sumCompl_apply_inr]
  rw [Finset.sum_congr rfl (fun x _ => ramificationIdx_eq_one K x.2.2),
    Finset.sum_congr rfl (fun x _ => ramificationIdx_eq_two K x.2.2),
    Finset.sum_const, Finset.sum_const, ← Fintype.card, ← Fintype.card, smul_eq_mul, mul_one,
    smul_eq_mul, mul_comm, ← card_isUnramified_add_two_mul_card_isRamified L v]

end NumberField.InfinitePlace.ExtensionPlace
