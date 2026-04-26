module

public import FLT.Patching.Algebra
public import FLT.Patching.Over
public import FLT.Patching.Module
public import FLT.Patching.Utils.Depth
public import FLT.Deformations.Lemmas

@[expose] public section

variable (Λ : Type*) [CommRing Λ]
variable {ι : Type*} (R : ι → Type*)
variable [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, Algebra Λ (R i)]
variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
variable [∀ i, CompactSpace (R i)] [∀ i, IsLocalRing.IsAdicTopology (R i)]

variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
variable [∀ i, Module (R i) (M i)] [∀ i, IsScalarTower Λ (R i) (M i)]
variable (F : Ultrafilter ι)
variable [TopologicalSpace Λ] [IsTopologicalRing Λ]
variable [IsLocalRing Λ] [IsNoetherianRing Λ] [NonarchimedeanRing Λ] [T2Space Λ]

attribute [local instance] Module.quotientAnnihilator

variable [Algebra.UniformlyBoundedRank R]
variable [∀ i, Module.Free (Λ ⧸ Module.annihilator Λ (M i)) (M i)]
variable [Module.UniformlyBoundedRank Λ M] [IsPatchingSystem Λ M F]

open IsLocalRing Module.UniformlyBoundedRank

open Pointwise in
instance {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [Module S M] [SMulCommClass S R M] : SMul (Ideal R) (Submodule S M) where
  smul I N := ⟨I.toAddSubmonoid • N.toAddSubmonoid, by
    intro r
    change I.toAddSubmonoid • N.toAddSubmonoid ≤
      (I.toAddSubmonoid • N.toAddSubmonoid).comap (DistribMulAction.toAddMonoidEnd S M r)
    rw [AddSubmonoid.smul_le]
    intro s hs n hn
    simp only [DistribMulAction.toAddMonoidEnd_apply, AddSubmonoid.mem_comap]
    change r • (s • n) ∈ _
    rw [smul_comm]
    exact AddSubmonoid.smul_mem_smul hs (N.smul_mem _ hn)⟩

open Pointwise in
lemma Submodule.map_algebraMap_smul {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [Module S M] [Algebra R S] [IsScalarTower R S M] (I : Ideal R)
    (N : Submodule S M) :
    I.map (algebraMap R S) • N = I • N := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr n hn
    induction hr using Submodule.span_induction with
    | mem x h =>
      obtain ⟨x, hx, rfl⟩ := h
      rw [algebraMap_smul]
      exact AddSubmonoid.smul_mem_smul hx hn
    | zero => exact zero_smul S n ▸ zero_mem _
    | add x y hx hy _ _ => rw [add_smul]; exact add_mem ‹_› ‹_›
    | smul a x hx _ => exact smul_assoc a x n ▸ (I • N).smul_mem _ ‹_›
  · change I.toAddSubmonoid • N.toAddSubmonoid ≤ _
    rw [AddSubmonoid.smul_le]
    intro r hr n hn
    rw [← algebraMap_smul S (M := M)]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) hn

variable [CompactSpace Λ] [∀ i, IsNoetherianRing (R i)]

omit
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [(i : ι) → TopologicalSpace (R i)]
  [IsLocalRing Λ]
  [IsNoetherianRing Λ]
  [NonarchimedeanRing Λ]
  [T2Space Λ]
  [Algebra.UniformlyBoundedRank R] in
lemma maximalIdeal_pow_bound_le_smul_top (i) (α : OpenIdeals Λ) :
    (maximalIdeal (R i) ^ (Nat.card (Λ ⧸ α.1) ^ bound Λ M) • ⊤ :
      Submodule (R i) (M i)) ≤ α.1 • ⊤ := by
  rw [← Submodule.map_algebraMap_smul α.1]
  let α' := α.1.map (algebraMap Λ (R i))
  have : Finite (Λ ⧸ α.1) := AddSubgroup.quotient_finite_of_isOpen _ α.2
  have : Finite (M i ⧸ (α' • ⊤ : Submodule (R i) (M i))) := by
    have := Module.UniformlyBoundedRank.finite_quotient_smul Λ M i α.1
    refine (QuotientAddGroup.quotientAddEquivOfEq ?_).toEquiv.finite_iff.mp this
    rw [Submodule.map_algebraMap_smul α.1]
    rfl
  refine le_trans ?_ (IsLocalRing.maximalIdeal_pow_card_smul_top_le (α' • ⊤))
  apply Submodule.smul_mono (Ideal.pow_le_pow_right ?_) le_rfl
  convert Module.UniformlyBoundedRank.card_quotient_le Λ M i α.1 using 1
  refine Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq ?_).toEquiv
  rw [Submodule.map_algebraMap_smul α.1]
  rfl

class PatchingAlgebra.smulData where
  f : OpenIdeals Λ → ℕ
  pow_f_smul_le : ∀ i α, (maximalIdeal (R i) ^ (f α) • ⊤ : Submodule (R i) (M i)) ≤ α.1 • ⊤
  f_mono : Antitone f


noncomputable
instance IsPatchingSystem.isModuleQuotient [PatchingAlgebra.smulData Λ R M] (α : OpenIdeals Λ) (i) :
    Module (R i ⧸ (maximalIdeal (R i) ^ (PatchingAlgebra.smulData.f R M α)))
      (M i ⧸ (α.1 • ⊤ : Submodule (R i) (M i))) := Module.IsTorsionBySet.module <| by
  rw [Module.isTorsionBySet_quotient_iff]
  intro r x hx
  exact PatchingAlgebra.smulData.pow_f_smul_le _ _ (Submodule.smul_mem_smul hx trivial)

noncomputable
instance IsPatchingSystem.isModuleQuotient' [PatchingAlgebra.smulData Λ R M]
    (α : OpenIdeals Λ) (i) :
    Module (R i ⧸ (maximalIdeal (R i) ^ (PatchingAlgebra.smulData.f R M α)))
      (M i ⧸ (α.1 • ⊤ : Submodule Λ (M i))) := IsPatchingSystem.isModuleQuotient ..

noncomputable
instance [PatchingAlgebra.smulData Λ R M] (α : OpenIdeals Λ) :
    Module (PatchingAlgebra.Component R F (PatchingAlgebra.smulData.f R M α))
      (PatchingModule.Component Λ M F α.1) := inferInstance

noncomputable
instance [PatchingAlgebra.smulData Λ R M] : SMul (PatchingAlgebra R F) (PatchingModule Λ M F) where
  smul x m := ⟨fun α ↦ x.1 (PatchingAlgebra.smulData.f R M α) • m.1 α, by
    intro α β h
    dsimp only [LinearMap.coe_restrictScalars]
    have : α.1.toAddSubgroup.FiniteIndex :=
      @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
        (AddSubgroup.quotient_finite_of_isOpen _ α.2)
    let n₁ := PatchingAlgebra.smulData.f R M α
    let n₂ := PatchingAlgebra.smulData.f R M β
    rw [← x.2 (PatchingAlgebra.smulData.f R M α) (PatchingAlgebra.smulData.f R M β)
      (PatchingAlgebra.smulData.f_mono h),
      ← m.2 α β h]
    generalize m.1 α = m
    generalize x.1 (PatchingAlgebra.smulData.f R M α) = x
    obtain ⟨x, rfl⟩ := UltraProduct.π_surjective x
    change UltraProduct.map _ _ (x • _) = _
    obtain ⟨m, rfl⟩ := UltraProduct.πₗ_surjective
      (fun i ↦ R i ⧸ maximalIdeal (R i) ^ (PatchingAlgebra.smulData.f R M α)) m
    rw [← map_smul]
    choose x hx using fun i ↦ Submodule.Quotient.mk_surjective _ (x i)
    obtain rfl := funext hx
    choose m hm using fun i ↦ Submodule.Quotient.mk_surjective _ (m i)
    obtain rfl := funext hm
    rfl⟩

noncomputable
instance [PatchingAlgebra.smulData Λ R M] : Module (PatchingAlgebra R F)
    (PatchingModule Λ M F) where
  one_smul _ := Subtype.ext <| funext fun _ ↦ one_smul _ _
  mul_smul _ _ _ := Subtype.ext <| funext fun _ ↦ mul_smul _ _ _
  smul_zero _ := Subtype.ext <| funext fun _ ↦ smul_zero _
  smul_add _ _ _ := Subtype.ext <| funext fun _ ↦ smul_add _ _ _
  add_smul _ _ _ := Subtype.ext <| funext fun _ ↦ add_smul _ _ _
  zero_smul r := Subtype.ext <| funext fun α ↦
    zero_smul (PatchingAlgebra.Component R F (PatchingAlgebra.smulData.f R M α)) (r.1 α)

instance [PatchingAlgebra.smulData Λ R M] :
    IsScalarTower Λ (PatchingAlgebra R F) (PatchingModule Λ M F) := .of_algebraMap_smul <| by
  intro r m
  refine Subtype.ext (funext fun α ↦ ?_)
  obtain ⟨x, hx⟩ := UltraProduct.πₗ_surjective (fun _ ↦ Λ) (m.1 α)
  change (algebraMap Λ (Π i, R i ⧸ maximalIdeal (R i) ^
    (PatchingAlgebra.smulData.f R M α)) r) • m.1 α = r • m.1 α
  rw [← hx]
  refine UltraProduct.πₗ_eq_iff.mpr (.of_forall fun i ↦ ?_)
  exact algebraMap_smul (M := M i ⧸ (α.1 • ⊤ : Submodule (R i) (M i))) (R i) r (x i)

instance [PatchingAlgebra.smulData Λ R M] : Module.Finite (PatchingAlgebra R F)
    (PatchingModule Λ M F) :=
  Module.Finite.of_restrictScalars_finite Λ _ _

set_option backward.isDefEq.respectTransparency false in
noncomputable
instance : PatchingAlgebra.smulData Λ R M where
  f α := α.1.toAddSubgroup.index ^ bound Λ M
  pow_f_smul_le i α := maximalIdeal_pow_bound_le_smul_top Λ R M i α
  f_mono α β h := by
    have : α.1.toAddSubgroup.FiniteIndex :=
      @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
        (AddSubgroup.quotient_finite_of_isOpen _ α.2)
    dsimp
    gcongr

variable {R₀ M₀ : Type*} [CommRing R₀] [AddCommGroup M₀] [Module R₀ M₀] [Module.Finite R₀ M₀]
variable [IsLocalRing R₀] [IsNoetherianRing R₀]
  [TopologicalSpace R₀] [IsTopologicalRing R₀] [CompactSpace R₀] [IsAdicTopology R₀]
variable [Algebra Λ R₀] [Module Λ M₀] [Module.Finite Λ M₀]
variable (𝔫 : Ideal Λ)
variable (sR : ∀ i, (R i ⧸ 𝔫.map (algebraMap Λ (R i))) ≃ₐ[Λ] R₀)
variable (sM : ∀ i, (M i ⧸ (𝔫 • ⊤ : Submodule Λ (M i))) ≃ₗ[Λ] M₀)

variable {Rₒₒ : Type*} [CommRing Rₒₒ] [IsNoetherianRing Rₒₒ] [IsLocalRing Rₒₒ] [IsDomain Rₒₒ]
    [Algebra Λ Rₒₒ]
variable [TopologicalSpace Rₒₒ] [CompactSpace Rₒₒ] [IsTopologicalRing Rₒₒ]
    [Algebra.TopologicallyFG ℤ Rₒₒ]
variable [IsLocalHom (algebraMap Λ Rₒₒ)]
variable (fRₒₒ : ∀ i, Rₒₒ →ₐ[Λ] R i)
variable (hfRₒₒ : ∀ i, Function.Surjective (fRₒₒ i)) (hfRₒₒ' : ∀ i, Continuous (fRₒₒ i))

variable [IsScalarTower Λ R₀ M₀]
variable [∀ i, Nontrivial (M i)]

noncomputable
instance : PatchingAlgebra.smulData Λ (fun _ : ι ↦ R₀) (fun _ ↦ M₀) := by
  classical
  suffices ∀ α : OpenIdeals Λ, ∃ i, (maximalIdeal R₀ ^ i • ⊤ : Submodule R₀ M₀) ≤ α.1 • ⊤ by
    refine ⟨fun α ↦ Nat.find (this α), fun _ α ↦ Nat.find_spec (this α),
      fun α β h ↦ Nat.find_min' (this β) ((Nat.find_spec (this α)).trans ?_)⟩
    rw [← Submodule.map_algebraMap_smul α.1, ← Submodule.map_algebraMap_smul β.1]
    exact (Submodule.smul_mono (Ideal.map_mono h) le_rfl)
  intro α
  rw [← Submodule.map_algebraMap_smul α.1]
  let α' := α.1.map (algebraMap Λ R₀)
  have : Finite (Λ ⧸ α.1) := AddSubgroup.quotient_finite_of_isOpen _ α.2
  have : Module.Finite (Λ ⧸ α.1) (M₀ ⧸ (α.1 • ⊤ : Submodule Λ M₀)) :=
    .of_restrictScalars_finite Λ _ _
  have : Finite (M₀ ⧸ (α.1 • ⊤ : Submodule Λ M₀)) := Module.finite_of_finite (Λ ⧸ α.1)
  have : Finite (M₀ ⧸ (α' • ⊤ : Submodule R₀ M₀)) := by
    refine (QuotientAddGroup.quotientAddEquivOfEq ?_).toEquiv.finite_iff.mp this
    rw [Submodule.map_algebraMap_smul α.1]
    rfl
  exact ⟨_, IsLocalRing.maximalIdeal_pow_card_smul_top_le (α' • ⊤)⟩

include hfRₒₒ hfRₒₒ' in
omit [IsNoetherianRing Λ] [IsNoetherianRing Rₒₒ] in
lemma PatchingAlgebra.faithfulSMul
    (H₀ : ringKrullDim Rₒₒ < ⊤)
    (H : .some (Module.depth Λ Λ) = ringKrullDim Rₒₒ) :
    FaithfulSMul (PatchingAlgebra R F) (PatchingModule Λ M F) := by
  let f := PatchingAlgebra.lift R F (fun i ↦ (fRₒₒ i).toRingHom)
  have hf : Function.Surjective f :=
    lift_surjective R F _ hfRₒₒ' hfRₒₒ
  have hf' (r) : f (algebraMap Λ _ r) = algebraMap Λ _ r := by
    refine Subtype.ext (funext fun k ↦ UltraProduct.π_eq_iff.mpr (.of_forall fun i ↦ ?_))
    simp
  letI := f.toAlgebra
  letI := Module.compHom (PatchingModule Λ M F) f
  suffices FaithfulSMul Rₒₒ (PatchingModule Λ M F) by
    refine ⟨fun {x₁ x₂} H ↦ ?_⟩
    obtain ⟨x₁, rfl⟩ := hf x₁
    obtain ⟨x₂, rfl⟩ := hf x₂
    obtain rfl : x₁ = x₂ := FaithfulSMul.eq_of_smul_eq_smul H
    rfl
  have : Nontrivial (PatchingModule Λ M F) := by
    by_contra H
    rw [not_nontrivial_iff_subsingleton] at H
    obtain ⟨i, ⟨e⟩⟩ := (Module.UniformlyBoundedRank.rank_spec Λ M F).exists
    have := PatchingModule.rank_patchingModule Λ M F
    simp only [rank_subsingleton', @eq_comm Cardinal 0, Nat.cast_eq_zero] at this
    have : Subsingleton (Fin (rank Λ M F) → Λ ⧸ Module.annihilator Λ (M i)) := by
      rw [this]
      infer_instance
    exact not_subsingleton _ e.subsingleton
  have : IsScalarTower Λ Rₒₒ (PatchingModule Λ M F) := .of_algebraMap_smul <| by
    intro r m
    conv_rhs => rw [← IsScalarTower.algebraMap_smul (PatchingAlgebra R F), ← hf']
    rfl
  have : Module.Finite Rₒₒ (PatchingModule Λ M F) :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  apply Module.faithfulSMul_of_depth_eq_ringKrullDim _ _ H₀
  refine le_antisymm (Module.depth_le_dim _ _) ?_
  have : Module.depth Λ Λ ≤ Module.depth Rₒₒ (PatchingModule Λ M F) :=
    (Module.depth_le_of_free _ _).trans (Module.depth_of_isScalarTower Λ _ _)
  rwa [← H, WithBot.coe_le_coe]

lemma Ultrafilter.eventually_eventually_eq_of_finite
    {α β : Type*} [Finite β] (F : Ultrafilter α) (f : α → β) :
    ∀ᶠ (i) (j) in F, f i = f j := by
  obtain ⟨a, ha⟩ : ∃ a, ∀ᶠ i in F, f i = a := Ultrafilter.eventually_exists_iff.mp (by simp)
  filter_upwards [ha] with i hi
  filter_upwards [ha] with j hj
  rw [hi, hj]

omit
  [∀ (i : ι), TopologicalSpace (R i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [IsLocalRing Λ]
  [IsNoetherianRing Λ]
  [NonarchimedeanRing Λ]
  [T2Space Λ]
  [Algebra.UniformlyBoundedRank R]
  [IsPatchingSystem Λ M ↑F]
  [Module.Finite R₀ M₀]
  [TopologicalSpace R₀]
  [IsTopologicalRing R₀]
  [CompactSpace R₀]
  [IsAdicTopology R₀]
  [∀ (i : ι), Nontrivial (M i)] in
lemma smul_lemma₀
    (HCompat : ∀ i m (r : R i), sM i (Submodule.Quotient.mk (r • m)) =
      sR i (Ideal.Quotient.mk _ r) • sM i (Submodule.Quotient.mk m))
    (x : PatchingModule Λ M F)
    (m : PatchingAlgebra R F)
    [∀ (i : ι), IsLocalHom (Ideal.Quotient.mk (𝔫.map (algebraMap Λ (R i))))] :
    PatchingModule.map Λ F (fun i ↦ (sM i).toLinearMap.comp (𝔫 • ⊤ : Submodule Λ (M i)).mkQ)
      (m • x) =
      PatchingAlgebra.map F (fun i ↦ (sR i).toRingHom.comp
        (Ideal.Quotient.mk (Ideal.map (algebraMap Λ (R i)) 𝔫))) m •
        PatchingModule.map Λ F (fun i ↦ (sM i).toLinearMap.comp
          (𝔫 • ⊤ : Submodule Λ (M i)).mkQ) x := by
  refine Subtype.ext (funext fun α ↦ ?_)
  obtain ⟨x, hx⟩ := x
  obtain ⟨m, hm⟩ := m
  obtain ⟨x, rfl⟩ := PatchingModule.ofPi_surjective x
  obtain ⟨m, rfl⟩ := PatchingAlgebra.ofPi_surjective m
  replace hm (i j h) := hm i j h
  simp only [PatchingAlgebra.ofPi_apply, UltraProduct.mapRingHom_π, Ideal.quotientMap_mk,
    RingHom.id_apply, UltraProduct.π_eq_iff] at hm
  let n₀ := PatchingAlgebra.smulData.f (fun _ : ι ↦ R₀) (fun _ ↦ M₀) α
  let n₁ := @PatchingAlgebra.smulData.f Λ _ _ R _ inferInstance _ M _ _ _ inferInstance _
    inferInstance α
  change UltraProduct.πₗ _ _ _ _ = UltraProduct.πₗ (fun _ ↦ R₀)
    (fun _ ↦ M₀ ⧸ (α.1 • ⊤ : Submodule R₀ M₀)) _ _
  refine UltraProduct.πₗ_eq_iff.mpr ?_
  filter_upwards [hm n₀ (min n₀ n₁) (min_le_left _ _), hm n₁ (min n₀ n₁) (min_le_right _ _)] with
    i hi₁ hi₂
  let F := (sR i).toRingHom.comp (Ideal.Quotient.mk _)
  have hF : Function.Surjective F := (sR i).surjective.comp Ideal.Quotient.mk_surjective
  have H : (maximalIdeal R₀ ^ (n₀ ⊓ n₁) • ⊤ : Submodule R₀ M₀) ≤ α.1 • ⊤ := by
    obtain h | h := le_total n₀ n₁
    · rw [min_eq_left h]; exact PatchingAlgebra.smulData.pow_f_smul_le i α
    · letI := F.toAlgebra
      letI := Module.compHom M₀ F
      have : IsScalarTower (R i) R₀ M₀ := .of_algebraMap_smul fun _ _ ↦ rfl
      have : IsScalarTower Λ (R i) R₀ := .of_algebraMap_eq' (sR i).toAlgHom.comp_algebraMap.symm
      let l : M i →ₗ[R i] M₀ :=
        { __ := (sM i).toLinearMap.comp (Submodule.mkQ _), map_smul' := fun _ _ ↦ HCompat _ _ _ }
      have hl : LinearMap.range l = ⊤ :=
        LinearMap.range_eq_top.mpr ((sM i).surjective.comp (Submodule.mkQ_surjective _))
      rw [min_eq_right h, ← IsLocalRing.map_maximalIdeal_of_surjective F hF, ← Ideal.map_pow]
      have : maximalIdeal (R i) ^ n₁ • ⊤ ≤ _ := PatchingAlgebra.smulData.pow_f_smul_le i α
      replace this := Submodule.map_mono (f := l) this
      rw [Submodule.map_smul'', ← Submodule.map_algebraMap_smul (R := Λ),
        Submodule.map_smul'', Submodule.map_top, hl] at this
      replace this : (maximalIdeal (R i) ^ n₁ • ⊤ : Submodule R₀ M₀) ≤
        α.1.map (algebraMap Λ (R i)) • ⊤ := this
      rwa [← Submodule.map_algebraMap_smul, ← Submodule.map_algebraMap_smul (R := R i),
        Ideal.map_map, ← IsScalarTower.algebraMap_eq,
        Submodule.map_algebraMap_smul (R := Λ)] at this
  refine (Submodule.Quotient.eq _).mpr ?_
  dsimp
  rw [HCompat, ← sub_smul, ← map_sub, ← map_sub]
  change F (m n₁ i - m n₀ i) • sM i _ ∈ _
  apply H
  refine Submodule.smul_mem_smul ?_ trivial
  rw [← Ideal.mem_comap]
  refine SetLike.le_def.mp ?_ ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (hi₂.trans hi₁.symm))
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, ← IsLocalRing.map_maximalIdeal_of_surjective F hF]

omit [NonarchimedeanRing Λ] [Module.Finite R₀ M₀] in
lemma smul_lemma₁
    (x : M₀)
    (m : R₀) :
    (PatchingModule.constEquiv Λ F M₀) (m • x) =
    (PatchingAlgebra.constEquiv F R₀) m • (PatchingModule.constEquiv Λ F M₀) x := rfl

omit
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [Algebra.UniformlyBoundedRank R]
  [IsPatchingSystem Λ M ↑F]
  [Module.Finite R₀ M₀]
  [∀ (i : ι), Nontrivial (M i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [(i : ι) → TopologicalSpace (R i)] in
lemma smul_lemma
    (HCompat : ∀ i m (r : R i), sM i (Submodule.Quotient.mk (r • m)) =
      sR i (Ideal.Quotient.mk _ r) • sM i (Submodule.Quotient.mk m))
    (m : PatchingAlgebra R F)
      (x : PatchingModule Λ M F ⧸ (𝔫 • ⊤ : Submodule (PatchingAlgebra R F)
      (PatchingModule Λ M F))) :
      PatchingModule.quotientEquivOver Λ M F 𝔫 sM (m • x) =
      ((PatchingAlgebra.quotientToOver Λ R F 𝔫 sR).comp (Ideal.Quotient.mk _)) m •
       PatchingModule.quotientEquivOver Λ M F 𝔫 sM x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  apply (PatchingModule.constEquiv Λ F M₀).injective
  refine ((PatchingModule.constEquiv Λ F M₀).apply_symm_apply _).trans ?_
  have (i : ι) : Nontrivial (R i ⧸ Ideal.map (algebraMap Λ (R i)) 𝔫) :=
    (sR i).toRingHom.domain_nontrivial
  have (i : ι) : IsLocalHom (Ideal.Quotient.mk (𝔫.map (algebraMap Λ (R i)))) :=
    .of_surjective _ (Ideal.Quotient.mk_surjective)
  convert smul_lemma₀ Λ R M F 𝔫 sR sM HCompat x m
  · obtain ⟨x, hx⟩ := x
    obtain ⟨m, hm⟩ := m
    obtain ⟨x, rfl⟩ := PatchingModule.ofPi_surjective x
    obtain ⟨m, rfl⟩ := PatchingAlgebra.ofPi_surjective m
    rfl
  rw [smul_lemma₁]
  congr 1
  · refine ((PatchingAlgebra.constEquiv F R₀).apply_symm_apply _).trans ?_
    obtain ⟨m, hm⟩ := m
    obtain ⟨m, rfl⟩ := PatchingAlgebra.ofPi_surjective m
    rfl
  · refine ((PatchingModule.constEquiv Λ F M₀).apply_symm_apply _).trans ?_
    obtain ⟨x, hx⟩ := x
    obtain ⟨x, rfl⟩ := PatchingModule.ofPi_surjective x
    rfl

include Λ R M F fRₒₒ hfRₒₒ hfRₒₒ' sR sM in
omit [Module.Finite R₀ M₀] [Module.Finite Λ M₀] [IsNoetherianRing Rₒₒ] in
lemma support_eq_top
    (HCompat : ∀ i m (r : R i), sM i (Submodule.Quotient.mk (r • m)) =
      sR i (Ideal.Quotient.mk _ r) • sM i (Submodule.Quotient.mk m))
    (H₀ : ringKrullDim Rₒₒ < ⊤)
    (H : .some (Module.depth Λ Λ) = ringKrullDim Rₒₒ) : Module.support R₀ M₀ = Set.univ := by
  have : Module.Finite Λ M₀ := by
    cases isEmpty_or_nonempty ι
    · cases F.neBot.1 (Subsingleton.elim _ _)
    have i := Nonempty.some (inferInstance: Nonempty ι)
    exact Module.Finite.equiv (sM i)
  have : Module.Finite R₀ M₀ := .of_restrictScalars_finite Λ _ _
  have := PatchingAlgebra.faithfulSMul Λ R M F fRₒₒ hfRₒₒ hfRₒₒ' H₀ H
  rw [Module.support_eq_zeroLocus, ← Set.univ_subset_iff]
  intro p hp
  let f₀ := ((PatchingAlgebra.quotientToOver Λ R F 𝔫 sR).comp (Ideal.Quotient.mk _))
  have hf₀ : Function.Surjective f₀ :=
    (PatchingAlgebra.surjective_quotientToOver Λ R F 𝔫 sR).comp Ideal.Quotient.mk_surjective
  let p' := PrimeSpectrum.comap f₀ p
  have hp' : 𝔫.map (algebraMap _ _) ≤ p'.asIdeal := by
    simp only [PrimeSpectrum.comap_comp, p', f₀]
    refine le_trans ?_ (Ideal.comap_mono (f := Ideal.Quotient.mk _) bot_le)
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  let inst := Module.compHom M₀ f₀
  letI := f₀.toAlgebra
  have : IsScalarTower (PatchingAlgebra R F) R₀ M₀ := .of_algebraMap_smul fun _ _ ↦ rfl
  let e' : (PatchingModule Λ M F ⧸ (𝔫 • ⊤ : Submodule (PatchingAlgebra R F) (PatchingModule Λ M F)))
    ≃ₗ[PatchingAlgebra R F] M₀ :=
    { __ := (PatchingModule.quotientEquivOver Λ M F 𝔫 sM),
      map_smul' := smul_lemma Λ R M F 𝔫 sR sM HCompat }
  have := congr(PrimeSpectrum.zeroLocus (R := PatchingAlgebra R F) ↑($(e'.annihilator_eq)))
  rw [← Submodule.map_algebraMap_smul, ← Module.support_eq_zeroLocus,
    Module.support_quotient,  Module.support_eq_zeroLocus,
    Module.annihilator_eq_bot.mpr inferInstance, ← Module.comap_annihilator (R := R₀),
    ← image_comap_zeroLocus_eq_zeroLocus_comap _ _ (by exact hf₀)] at this
  simp only [Submodule.bot_coe, PrimeSpectrum.zeroLocus_singleton_zero, Set.univ_inter] at this
  exact (PrimeSpectrum.comap_injective_of_surjective _ hf₀).mem_set_image.mp (this.le hp')
