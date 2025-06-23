import FLT.Patching.Algebra
import FLT.Patching.Module

variable (Λ : Type*) [CommRing Λ]
variable {ι : Type*} (R : ι → Type*)
variable [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, Algebra Λ (R i)]
variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
variable [∀ i, CompactSpace (R i)] [∀ i, IsLocalRing.IsAdicTopology (R i)]
variable (F : Ultrafilter ι)

variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
variable [∀ i, Module (R i) (M i)] [∀ i, IsScalarTower Λ (R i) (M i)]
variable (F : Ultrafilter ι)
variable [TopologicalSpace Λ] [IsTopologicalRing Λ] [∀ i, ContinuousSMul Λ (R i)]
variable [IsLocalRing Λ] [IsNoetherianRing Λ] [NonarchimedeanRing Λ] [T2Space Λ]
  [Algebra.TopologicallyFG ℤ Λ]

attribute [local instance] Module.quotientAnnihilator

variable [Algebra.UniformlyBoundedRank R]
variable [∀ i, Module.Free (Λ ⧸ Module.annihilator Λ (M i)) (M i)]
variable [Module.UniformlyBoundedRank Λ M] [IsPatchingSystem Λ M F]

variable {R₀ M₀ : Type*} [CommRing R₀] [AddCommGroup M₀] [Module R₀ M₀] [Algebra Λ R₀] [Module Λ M₀]
variable (𝔫 : Ideal Λ)
variable (sR : ∀ i, (R i ⧸ 𝔫.map (algebraMap Λ (R i))) ≃ₐ[Λ] R₀)
variable (sM : ∀ i, (M i ⧸ (𝔫 • ⊤ : Submodule Λ (M i))) ≃ₗ[Λ] M₀)

def Submodule.liftModIdeal {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {I : Ideal R}
    (f : M ⧸ (I • ⊤ : Submodule R M) →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) (J : Ideal R) :
    (M ⧸ (J • ⊤ : Submodule R M)) ⧸ (I • ⊤ : Submodule R (M ⧸ (J • ⊤ : Submodule R M))) →ₗ[R]
    (N ⧸ (J • ⊤ : Submodule R N)) ⧸ (I • ⊤ : Submodule R (N ⧸ (J • ⊤ : Submodule R N))) := by
  refine Submodule.liftQ _ (Submodule.liftQ _ (Submodule.mapQ _ _ (Submodule.mkQ _)
    ?_ ∘ₗ f ∘ₗ Submodule.mkQ _) ?_) ?_
  · rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  · rw [LinearMap.ker_comp, ← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.mapQ,
      Submodule.ker_liftQ, LinearMap.ker_comp]
    refine le_trans ?_ (Submodule.map_mono (Submodule.comap_mono bot_le))
    rw [Submodule.comap_bot, Submodule.ker_mkQ, Submodule.map_smul'']
    refine Submodule.smul_mono le_rfl (le_top.trans_eq ?_)
    rw [eq_comm, Submodule.map_top, LinearMap.range_eq_top]
    exact Submodule.mkQ_surjective _
  · rw [Submodule.ker_liftQ, ← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
      ← Submodule.map_top, ← Submodule.map_smul'']
    apply Submodule.map_mono
    rw [LinearMap.ker_comp, ← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    refine ((Submodule.smul_mono le_rfl le_top).trans ?_).trans bot_le
    rw [← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
      ← Submodule.map_top, ← Submodule.map_smul'', Submodule.map_le_iff_le_comap,
      Submodule.comap_bot, Submodule.ker_mkQ]

def Submodule.liftModIdealEquiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {I : Ideal R}
    (f : (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) (J : Ideal R) :
    ((M ⧸ (J • ⊤ : Submodule R M)) ⧸ (I • ⊤ : Submodule R (M ⧸ (J • ⊤ : Submodule R M)))) ≃ₗ[R]
    (N ⧸ (J • ⊤ : Submodule R N)) ⧸ (I • ⊤ : Submodule R (N ⧸ (J • ⊤ : Submodule R N))) where
  __ := liftModIdeal f J
  invFun := liftModIdeal f.symm J
  left_inv x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f (Submodule.Quotient.mk x))
    have hy' : f.symm (Quotient.mk y) = Quotient.mk x := by simpa using congr(f.symm $hy)
    simp [liftModIdeal, ← hy, hy']
  right_inv x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f.symm (Submodule.Quotient.mk x))
    have hy' : f (Quotient.mk y) = Quotient.mk x := by simpa using congr(f $hy)
    simp [liftModIdeal, ← hy, hy']

variable [CompactSpace Λ]

open IsLocalRing Module.UniformlyBoundedRank

instance : Subsingleton (PatchingModule.Component Λ M F ⊤) :=
  Module.subsingleton (Λ ⧸ (⊤ : Ideal Λ)) _

omit [IsNoetherianRing Λ]
  [NonarchimedeanRing Λ]
  [T2Space Λ]
  [Algebra.TopologicallyFG ℤ Λ]
  [IsPatchingSystem Λ M F]
  [IsLocalRing Λ] in
-- attribute [local instance] UltraProduct.instIsScalarTower in
lemma PatchingModule.ker_componentMapModule_mkQ (α : OpenIdeals Λ) :
    LinearMap.ker ((componentMapModule Λ F (fun i ↦
      (𝔫 • ⊤ : Submodule Λ (M i)).mkQ) α.1).restrictScalars Λ) = 𝔫 • ⊤ := by
  obtain ⟨α, hα₁⟩ := α
  classical
  set f := componentMapModule Λ F (fun i ↦ (𝔫 • ⊤ : Submodule Λ (M i)).mkQ) α
  have : Finite (Λ ⧸ α) := AddSubgroup.quotient_finite_of_isOpen _ hα₁
  let M₁ := fun i ↦ M i ⧸ (α • ⊤ : Submodule Λ (M i))
  let M₂ := fun i ↦ (M i ⧸ (𝔫 • ⊤ : Submodule Λ (M i))) ⧸
    (α • ⊤ : Submodule Λ (M i ⧸ (𝔫 • ⊤ : Submodule Λ (M i))))
  have h₀ (j) : (α • ⊤ : Submodule Λ (M j)) ≤
      Submodule.comap (𝔫 • ⊤ : Submodule Λ (M j)).mkQ (α • ⊤) := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  let π (j) : M₁ j →ₗ[Λ] M₂ j := Submodule.mapQ _ _ (Submodule.mkQ _) (h₀ j)
  have (i) : Finite (M₂ i) := by
    have := Module.UniformlyBoundedRank.finite_quotient_smul Λ M i α
    refine Finite.of_surjective (π i) ?_
    simp only [Submodule.mapQ, ← LinearMap.range_eq_top, Submodule.range_liftQ, M₁, M₂, π,
      LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top]
  have H₁ := UltraProduct.exists_bijective_of_bddAbove_card (R₀ := Λ ⧸ α) (M := M₁) F
    (Nat.card (Λ ⧸ α) ^ bound Λ M).succ
    (.of_forall fun i ↦ ⟨Module.UniformlyBoundedRank.finite_quotient_smul Λ M i α,
      (Module.UniformlyBoundedRank.card_quotient_le Λ M i α).trans_lt (Nat.lt_succ_self _)⟩)
  obtain ⟨i, ⟨H, hi₁⟩⟩ := H₁.exists
  let g₁ (j) : M₁ i →ₗ[Λ] M₁ j := (if h : Nonempty (M₁ i ≃ₗ[Λ ⧸ α] M₁ j) then
    h.some.toLinearMap else 0).restrictScalars Λ
  replace hi₁ : Function.Bijective ((UltraProduct.πₗ (fun _ ↦ Λ) M₁ F).restrictScalars Λ ∘ₗ
    LinearMap.pi g₁) := hi₁
  let g₂ (j) : M₂ i →ₗ[Λ] M₂ j := Submodule.liftModIdeal (g₁ j) 𝔫
  have hg₂ : ∀ᶠ j in F, Function.Bijective (g₂ j) := by
    filter_upwards [H] with j hj
    have : Function.Bijective (g₁ j) := by simpa only [g₁, dif_pos hj] using hj.some.bijective
    exact (Submodule.liftModIdealEquiv (.ofBijective _ this) 𝔫).bijective
  have hi₂ : Function.Bijective ((UltraProduct.πₗ (fun _ ↦ Λ) M₂ F).restrictScalars Λ ∘ₗ
      LinearMap.pi g₂) :=
    UltraProduct.bijective_of_eventually_bijective _ _ hg₂
  let e₁ := (LinearEquiv.ofBijective _ hi₁).restrictScalars Λ
  let e₂ := (LinearEquiv.ofBijective _ hi₂).restrictScalars Λ
  have h₀ : (α • ⊤ : Submodule Λ (M i)) ≤
      Submodule.comap (𝔫 • ⊤ : Submodule Λ (M i)).mkQ (α • ⊤) := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  have : f.restrictScalars Λ = e₂.toLinearMap ∘ₗ Submodule.mapQ _ _ (Submodule.mkQ _) h₀ ∘ₗ
      e₁.symm.toLinearMap := by
    ext x
    obtain ⟨x, rfl⟩ := e₁.surjective x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    show _ = e₂ ((α • ⊤ : Submodule Λ (M i)).mapQ (α • ⊤) (𝔫 • ⊤ : Submodule Λ (M i)).mkQ h₀
      (e₁.symm (e₁ _)))
    rw [e₁.symm_apply_apply]
    rfl
  rw [this]
  simp only [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  apply Submodule.map_injective_of_injective (f := e₁.symm.toLinearMap) e₁.symm.injective
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.map_comap_eq]
  simp only [LinearEquiv.range, le_top, inf_of_le_right, LinearMap.ker_restrictScalars, M₁]
  rw [Submodule.mapQ, Submodule.ker_liftQ, LinearMap.ker_comp, Submodule.ker_mkQ,
    Submodule.comap_smul_of_surjective _ _ (Submodule.mkQ_surjective _)]
  simp only [Submodule.comap_top, Submodule.ker_mkQ, Submodule.map_sup, Submodule.map_smul'',
    Submodule.map_top, Submodule.range_mkQ, Submodule.sup_smul]
  simp only [sup_eq_right]
  refine le_trans ?_ bot_le
  rw [← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
      ← Submodule.map_top, ← Submodule.map_smul'', Submodule.map_le_iff_le_comap,
      Submodule.comap_bot, Submodule.ker_mkQ]

omit  [Algebra.TopologicallyFG ℤ Λ]
  [IsPatchingSystem Λ M F] [NonarchimedeanRing Λ] in
lemma PatchingModule.mem_smul_top (x : PatchingModule Λ M F) :
    x ∈ (𝔫 • ⊤ : Submodule Λ (PatchingModule Λ M F)) ↔
      ∀ (α : OpenIdeals Λ), x.1 α ∈ (𝔫 • ⊤ : Submodule Λ (Component Λ M F α.1)) := by
  classical
  constructor
  · intro H α
    replace H := Submodule.mem_map_of_mem (f := (submodule Λ M F).subtype.restrictScalars Λ) H
    replace H := Submodule.mem_map_of_mem (f := LinearMap.proj α) H
    simp only [Submodule.map_smul''] at H
    exact SetLike.le_def.mp (Submodule.smul_mono le_rfl le_top) H
  · intro H
    obtain ⟨s₀, hs⟩ := IsNoetherian.noetherian 𝔫
    let X (α : OpenIdeals Λ) := s₀ →₀ Component Λ M F α.1
    have (α : OpenIdeals Λ) : Fintype (Component Λ M F α.1) :=
      (nonempty_fintype (Component Λ M F α.1)).some
    let f (α) : X α →ₗ[Λ] Component Λ M F α.1 := Finsupp.lsum Λ fun x ↦ Module.toModuleEnd _ _ x.1
    let s (α) : Set (X α) := (f α) ⁻¹' {x.1 α}
    let t {α β} (h : α ≤ β) (a : s α) : s β :=
      ⟨Finsupp.mapRange.linearMap (componentMap Λ M F h) a.1, by
        obtain ⟨a, ha⟩ := a
        simp only [LinearMap.coe_restrictScalars,
          Set.mem_preimage, Set.mem_singleton_iff, s] at ha ⊢
        rw [← x.2 _ _ h, ← ha, ← LinearMap.comp_apply, ← LinearMap.comp_apply]
        congr 1
        ext
        simp only [Module.toModuleEnd_apply, LinearMap.coe_comp, Finsupp.coe_lsum,
          Function.comp_apply, Finsupp.lsingle_apply, Finsupp.mapRange.linearMap_apply,
          LinearMap.coe_restrictScalars, Finsupp.mapRange_single,
          DistribMulAction.toLinearMap_apply, smul_zero, Finsupp.sum_single_index,
          LinearMap.map_smul_of_tower, X, f]⟩
    have ht₁ (α) : t (α := α) le_rfl = id := by
      ext a b
      obtain ⟨c, hc⟩ := UltraProduct.πₗ_surjective (fun _ ↦ Λ) (a.1 b)
      simp only [Finsupp.mapRange.linearMap_apply, LinearMap.coe_restrictScalars, Submodule.mapQ_id,
        Finsupp.mapRange_apply, ← hc, UltraProduct.map_πₗ, LinearMap.id_coe, id_eq, t]
    have ht₂ (α β γ) (h₁ : α ≤ β) (h₂ : β ≤ γ) : t h₂ ∘ t h₁ = t (h₁.trans h₂) := by
      ext a b
      obtain ⟨c, hc⟩ := UltraProduct.πₗ_surjective (fun _ ↦ Λ) (a.1 b)
      simp only [Function.comp_apply, Finsupp.mapRange.linearMap_apply,
        LinearMap.coe_restrictScalars, Finsupp.mapRange_mapRange, Finsupp.mapRange_apply, ← hc,
        UltraProduct.map_πₗ, UltraProduct.πₗ_eq_iff, t]
      filter_upwards with i
      obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (c i)
      simp only [← hd, Submodule.mapQ_apply, LinearMap.id_coe, id_eq]
    have (α) : Nonempty (s α) := by
      simp only [nonempty_subtype, Set.mem_preimage, Set.mem_singleton_iff, s]
      suffices 𝔫 • ⊤ ≤ LinearMap.range (f α) from this (H α)
      refine Submodule.smul_le.mpr fun r hr m hm ↦ ?_
      rw [← hs] at hr
      induction hr using Submodule.span_induction with
      | mem x h =>
        refine ⟨Finsupp.single ⟨x, h⟩ m, ?_⟩
        simp only [Module.toModuleEnd_apply, X, f, smul_zero,
          Finsupp.coe_lsum, DistribMulAction.toLinearMap_apply, Finsupp.sum_single_index]
      | zero => simp only [zero_smul, Submodule.zero_mem]
      | add x y hx hy hx' hy' => simpa only [add_smul] using add_mem hx' hy'
      | smul a x hx hx' => simpa only [smul_assoc] using Submodule.smul_mem _ a hx'
    obtain ⟨⟨v, hv⟩⟩ := nonempty_inverseLimit_of_finite (fun α ↦ s α) (fun α β ↦ t)
      ht₁ ht₂ (l := fun i ↦ ⟨maximalIdeal Λ ^ i, isOpen_maximalIdeal_pow _ _⟩)
      (fun _ _ h ↦ Ideal.pow_le_pow_right h)
      (fun α ↦ have : Finite (Λ ⧸ α.1) := AddSubgroup.quotient_finite_of_isOpen _ α.2
        exists_maximalIdeal_pow_le_of_finite_quotient _)
    let y : s₀ →₀ PatchingModule Λ M F := Finsupp.equivFunOnFinite.symm fun a ↦
      ⟨fun i ↦ (v i).1 a, fun α β h ↦ by
        simp only [LinearMap.coe_restrictScalars, ← hv α β h, Finsupp.mapRange.linearMap_apply,
          X, s, Finsupp.mapRange_apply, t]⟩
    have : Finsupp.lsum Λ (fun x : s₀ ↦ Module.toModuleEnd Λ _ x.1) y = x := by
      refine Subtype.ext (funext fun α ↦ ?_)
      have : _ = _ := (v α).2
      simp only [PatchingModule, Module.toModuleEnd_apply, Finsupp.coe_lsum,
        DistribMulAction.toLinearMap_apply, smul_zero, implies_true, Finsupp.sum_fintype,
        Finset.univ_eq_attach, Finsupp.equivFunOnFinite_symm_apply_toFun,
        AddSubmonoidClass.coe_finset_sum, SetLike.val_smul_of_tower, Finset.sum_apply,
        Pi.smul_apply, ← this, y, X, s, f]
    rw [← this]
    simp only [Module.toModuleEnd_apply, Finsupp.coe_lsum, DistribMulAction.toLinearMap_apply,
      smul_zero, implies_true, Finsupp.sum_fintype, Finset.univ_eq_attach]
    exact sum_mem fun x _ ↦ Submodule.smul_mem_smul
      (by rw [← hs]; exact Submodule.subset_span x.2) trivial

omit  [Algebra.TopologicallyFG ℤ Λ]
  [IsPatchingSystem Λ M F] [NonarchimedeanRing Λ] in
lemma PatchingModule.ker_map_mkQ :
    LinearMap.ker ((PatchingModule.map Λ F fun i ↦
      (𝔫 • ⊤ : Submodule Λ (M i)).mkQ).restrictScalars Λ) = 𝔫 • ⊤ := by
  apply le_antisymm
  · rintro ⟨x, hx⟩ H
    replace H (α) : x α ∈ (𝔫 • ⊤ : Submodule Λ (Component Λ M F α.1)) := by
      have : x α ∈ LinearMap.ker ((componentMapModule Λ F (fun i ↦
        (𝔫 • ⊤ : Submodule Λ (M i)).mkQ) α.1).restrictScalars Λ) := congr_fun
          (congr_arg Subtype.val H) α
      rwa [PatchingModule.ker_componentMapModule_mkQ] at this
    rwa [PatchingModule.mem_smul_top]
  · rw [Submodule.smul_le]
    rintro r hr x -
    refine Subtype.ext (funext fun α ↦ ?_)
    obtain ⟨y, hy⟩ := ofPi_surjective x.1
    simp only [LinearMap.map_smulₛₗ, RingHom.id_apply, LinearMap.coe_restrictScalars, ←
      LinearMap.map_smul_of_tower, map_apply, smul_apply, ← hy, ofPi_apply, UltraProduct.map_πₗ,
      Pi.smul_apply, ← Submodule.Quotient.mk_smul, Submodule.mapQ_apply, Submodule.mkQ_apply,
      ZeroMemClass.coe_zero, Pi.zero_apply, UltraProduct.πₗ_eq_zero, Submodule.Quotient.mk_eq_zero]
    simp only [← Submodule.mkQ_apply, ← Submodule.mem_comap,
      Submodule.comap_smul_of_surjective _ _ (Submodule.mkQ_surjective _),
      Submodule.comap_top, Submodule.ker_mkQ, ← Submodule.sup_smul]
    filter_upwards with i
    exact Submodule.smul_mem_smul (Ideal.mem_sup_right hr) trivial

noncomputable
def PatchingModule.quotientTo :
    (PatchingModule Λ M F ⧸ (𝔫 • ⊤ : Submodule Λ (PatchingModule Λ M F))) →ₗ[Λ]
      PatchingModule Λ (fun i ↦ (M i) ⧸ (𝔫 • ⊤ : Submodule Λ (M i))) F :=
  Submodule.liftQ _
    ((PatchingModule.map Λ F fun _ ↦ Submodule.mkQ _).restrictScalars Λ) (ker_map_mkQ Λ M F 𝔫).ge

noncomputable
def PatchingModule.quotientEquiv :
    (PatchingModule Λ M F ⧸ (𝔫 • ⊤ : Submodule Λ (PatchingModule Λ M F))) ≃ₗ[Λ]
      PatchingModule Λ (fun i ↦ (M i) ⧸ (𝔫 • ⊤ : Submodule Λ (M i))) F := by
  refine LinearEquiv.ofBijective (quotientTo Λ M F 𝔫) ⟨?_, ?_⟩
  · rw [quotientTo, ← LinearMap.ker_eq_bot, Submodule.ker_liftQ, eq_bot_iff,
      Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ, ker_map_mkQ]
  · rw [quotientTo, ← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
    exact PatchingModule.map_surjective Λ F _ (fun i ↦ Submodule.mkQ_surjective _)

noncomputable
def PatchingModule.quotientEquivOver [Module.Finite Λ M₀] :
    (PatchingModule Λ M F ⧸ (𝔫 • ⊤ : Submodule Λ (PatchingModule Λ M F))) ≃ₗ[Λ] M₀ :=
  quotientEquiv Λ M F 𝔫 ≪≫ₗ (mapEquiv Λ F (by exact sM)).restrictScalars Λ ≪≫ₗ
    (constEquiv Λ F M₀).symm

variable [IsLocalRing R₀] [IsNoetherianRing R₀]
  [TopologicalSpace R₀] [IsTopologicalRing R₀] [CompactSpace R₀] [IsAdicTopology R₀]

noncomputable
def PatchingAlgebra.quotientTo
    [∀ (i : ι), IsLocalRing (R i ⧸ Ideal.map (algebraMap Λ (R i)) 𝔫)] :
    (PatchingAlgebra R F ⧸ 𝔫.map (algebraMap Λ (PatchingAlgebra R F))) →+*
      PatchingAlgebra (fun i ↦ R i ⧸ 𝔫.map (algebraMap Λ (R i))) F :=
  letI : ∀ (i : ι), IsLocalHom ((fun i ↦ Ideal.Quotient.mk (𝔫.map (algebraMap Λ (R i)))) i) :=
    fun i ↦ .of_surjective _ Ideal.Quotient.mk_surjective
  Ideal.Quotient.lift _ (map F (fun i ↦ Ideal.Quotient.mk (𝔫.map (algebraMap Λ (R i))))) <| by
    show 𝔫.map (algebraMap Λ (PatchingAlgebra R F)) ≤ RingHom.ker _
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    refine Subtype.ext (funext fun k ↦ UltraProduct.π_eq_zero_iff.mpr ?_)
    simp only [Pi.ringHom_apply, RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
      Pi.algebraMap_apply, Ideal.quotientMap_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    filter_upwards with i
    convert Ideal.zero_mem _ using 1
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hx

noncomputable
def PatchingAlgebra.quotientToOver :
    (PatchingAlgebra R F ⧸ 𝔫.map (algebraMap Λ (PatchingAlgebra R F))) →+* R₀ :=
  haveI (i) : Nontrivial (R i ⧸ Ideal.map (algebraMap Λ (R i)) 𝔫) :=
    (sR i).toRingHom.domain_nontrivial
  haveI (i) : IsLocalRing (R i ⧸ Ideal.map (algebraMap Λ (R i)) 𝔫) :=
    .of_surjective' (sR i).symm.toRingHom (sR i).symm.surjective
  ((constEquiv F R₀).symm.toRingHom.comp
    (mapEquiv _ _ (fun i ↦ (sR i).toRingEquiv)).toRingHom).comp (quotientTo Λ R F 𝔫)

omit
  [TopologicalSpace Λ]
  [IsTopologicalRing Λ]
  [∀ (i : ι), ContinuousSMul Λ (R i)]
  [IsLocalRing Λ]
  [IsNoetherianRing Λ]
  [NonarchimedeanRing Λ]
  [T2Space Λ]
  [Algebra.TopologicallyFG ℤ Λ]
  [CompactSpace Λ] in
lemma PatchingAlgebra.surjective_quotientToOver :
    Function.Surjective (quotientToOver Λ R F 𝔫 sR) := by
  haveI (i) : Nontrivial (R i ⧸ Ideal.map (algebraMap Λ (R i)) 𝔫) :=
    (sR i).toRingHom.domain_nontrivial
  haveI (i) : IsLocalRing (R i ⧸ Ideal.map (algebraMap Λ (R i)) 𝔫) :=
    .of_surjective' (sR i).symm.toRingHom (sR i).symm.surjective
  letI : ∀ (i : ι), IsLocalHom ((fun i ↦ Ideal.Quotient.mk (𝔫.map (algebraMap Λ (R i)))) i) :=
    fun i ↦ .of_surjective _ Ideal.Quotient.mk_surjective
  refine (constEquiv F R₀).symm.surjective.comp ?_
  refine (mapEquiv _ _ (fun i ↦ (sR i).toRingEquiv)).surjective.comp ?_
  apply Ideal.Quotient.lift_surjective_of_surjective
  apply PatchingAlgebra.map_surjective
  exact fun _ ↦ Ideal.Quotient.mk_surjective
