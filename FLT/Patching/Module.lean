import FLT.Patching.Utils.AdicTopology
import FLT.Patching.Ultraproduct
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Algebra.Module.Torsion
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

local notation "Ann" => Module.annihilator

attribute [local instance] Module.quotientAnnihilator

section

open Submodule

variable {ι : Type*} (R : Type*) (M : ι → Type*) [CommRing R]
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (F : Ultrafilter ι)

class Module.UniformlyBoundedRank : Prop where
  cond : ∃ n : ℕ, ∀ i, Module.rank (R ⧸ Ann R (M i)) (M i) < n

variable [Module.UniformlyBoundedRank R M]

noncomputable
def Module.UniformlyBoundedRank.bound : ℕ :=
  Module.UniformlyBoundedRank.cond (R := R) (M := M).choose

lemma Module.UniformlyBoundedRank.rank_lt_bound (i) :
    Module.rank (R ⧸ Ann R (M i)) (M i) < bound R M :=
  Module.UniformlyBoundedRank.cond (R := R) (M := M).choose_spec i

lemma Module.UniformlyBoundedRank.finrank_lt_bound (i) :
    Module.finrank (R ⧸ Ann R (M i)) (M i) < bound R M :=
  finrank_lt_of_rank_lt (rank_lt_bound R M i)

variable [∀ i, Module.Free (R ⧸ Ann R (M i)) (M i)]

instance (i) : Module.Finite (R ⧸ Ann R (M i)) (M i) :=
  Module.finite_of_rank_eq_nat (Cardinal.cast_toNat_of_lt_aleph0
    ((Module.UniformlyBoundedRank.rank_lt_bound R M i).trans (Cardinal.nat_lt_aleph0 _))).symm

instance (i) : Module.Finite R (M i) := Module.Finite.trans (R ⧸ Ann R (M i)) (M i)

lemma Module.UniformlyBoundedRank.exists_finsupp_surjective (i) :
    ∃ f : ((Fin (bound R M)) →₀ R) →ₗ[R] M i, Function.Surjective f := by
  cases subsingleton_or_nontrivial (M i)
  · refine ⟨0, fun x ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  have : Nontrivial (R ⧸ Ann R (M i)) := by
    refine Ideal.Quotient.nontrivial ?_
    rw [ne_eq, ← annihilator_top, Submodule.annihilator_eq_top_iff]
    exact top_ne_bot
  refine ⟨((Module.Free.chooseBasis (R ⧸ Ann R (M i)) (M i)).repr.symm.restrictScalars R).toLinearMap ∘ₗ ?_, ?_⟩
  · refine Finsupp.mapRange.linearMap (Algebra.linearMap R (R ⧸ Ann R (M i))) ∘ₗ Finsupp.lcomapDomain ?_ ?_
    · exact fun x ↦ Fin.castLE
        (by rw [← finrank_eq_card_chooseBasisIndex]; exact (finrank_lt_bound R M i).le)
        (Fintype.equivFin _ x)
    · exact (Fin.castLE_injective _).comp (Fintype.equivFin _).injective
  · simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective]
    refine (Finsupp.mapRange_surjective _ (map_zero _) Ideal.Quotient.mk_surjective).comp ?_
    exact Finsupp.comapDomain_surjective _ ((Fin.castLE_injective _).comp (Fintype.equivFin _).injective)

lemma Module.UniformlyBoundedRank.finite_quotient_smul (i) (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (M i ⧸ (I • ⊤ : Submodule R (M i))) := by
  obtain ⟨f, hf⟩ := exists_finsupp_surjective R M i
  let f' : (Fin (bound R M) → R ⧸ I) →ₗ[R] M i ⧸ (I • ⊤ : Submodule R (M i)) :=
    Pi.liftQuotientₗ (f ∘ₗ (Finsupp.linearEquivFunOnFinite _ _ _).symm.toLinearMap) _
  have hf' : Function.Surjective f' :=
    Pi.liftQuotientₗ_surjective _ _ (hf.comp (LinearEquiv.surjective _))
  exact _root_.Finite.of_surjective _ hf'

lemma Module.UniformlyBoundedRank.card_quotient_le (i) (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (M i ⧸ (I • ⊤ : Submodule R (M i))) ≤ (Nat.card (R ⧸ I)) ^ bound R M := by
  obtain ⟨f, hf⟩ := exists_finsupp_surjective R M i
  let f' : (Fin (bound R M) → R ⧸ I) →ₗ[R] M i ⧸ (I • ⊤ : Submodule R (M i)) :=
    Pi.liftQuotientₗ (f ∘ₗ (Finsupp.linearEquivFunOnFinite _ _ _).symm.toLinearMap) _
  have hf' : Function.Surjective f' :=
    Pi.liftQuotientₗ_surjective _ _ (hf.comp (LinearEquiv.surjective _))
  refine (Nat.card_le_card_of_surjective _ hf').trans_eq ?_
  cases nonempty_fintype (R ⧸ I)
  simp

lemma Module.UniformlyBoundedRank.exists_rank :
    ∃ n : ℕ, ∀ᶠ i in F, Nonempty (M i ≃ₗ[R] Fin n → R ⧸ Ann R (M i)) := by
  let n := bound R M
  suffices ∃ i : Fin (n + 1), ∀ᶠ j in F, Nonempty (M j ≃ₗ[R] Fin i → R ⧸ Ann R (M j)) by
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  rw [← Ultrafilter.eventually_exists_iff]
  refine .of_forall fun i ↦ ?_
  cases subsingleton_or_nontrivial (M i)
  · refine ⟨0, by simpa using ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  have : Nontrivial (R ⧸ Ann R (M i)) := by
    refine Ideal.Quotient.nontrivial ?_
    rw [ne_eq, ← annihilator_top, Submodule.annihilator_eq_top_iff]
    exact top_ne_bot
  refine ⟨⟨_,(Module.finrank_lt_of_rank_lt (rank_lt_bound R M i)).trans_le n.le_succ⟩, ⟨?_⟩⟩
  refine (Module.Free.chooseBasis (R ⧸ Ann R (M i)) (M i)).repr.restrictScalars R ≪≫ₗ ?_
  refine Finsupp.linearEquivFunOnFinite _ _ _ ≪≫ₗ ?_
  refine LinearEquiv.funCongrLeft R (R ⧸ Ann R (M i)) (Fintype.equivOfCardEq ?_)
  simp [Module.finrank_eq_card_chooseBasisIndex]

noncomputable
def Module.UniformlyBoundedRank.rank : ℕ := (exists_rank R M F).choose

lemma Module.UniformlyBoundedRank.rank_spec :
    ∀ᶠ i in F, Nonempty (M i ≃ₗ[R] Fin (rank R M F) → R ⧸ Ann R (M i)) :=
  (exists_rank R M F).choose_spec

noncomputable
def Module.UniformlyBoundedRank.linearMap (i) :
    (Fin (rank R M F) → R) →ₗ[R] M i :=
  letI := Classical.propDecidable
  if h : Nonempty (M i ≃ₗ[R] Fin (rank R M F) → R ⧸ Ann R (M i)) then
    h.some.symm.toLinearMap ∘ₗ ((Algebra.linearMap _ _).compLeft (Fin (rank R M F)))
  else 0

lemma Module.UniformlyBoundedRank.linearMap_surjective :
    ∀ᶠ i in F, Function.Surjective (linearMap R M F i) := by
  filter_upwards [rank_spec R M F] with i hi
  rw [linearMap, dif_pos hi]
  exact hi.some.symm.surjective.comp
    (Function.Surjective.comp_left Ideal.Quotient.mk_surjective)

lemma Module.UniformlyBoundedRank.linearMap_eq_zero :
    ∀ᶠ i in F, ∀ x, linearMap R M F i x = 0 ↔ ∀ j, x j ∈ Ann R (M i) := by
  filter_upwards [rank_spec R M F] with i hi x
  rw [linearMap, dif_pos hi]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    EmbeddingLike.map_eq_zero_iff, funext_iff]
  apply forall_congr' fun j ↦ ?_
  simp [Ideal.Quotient.eq_zero_iff_mem]

end

variable (R : Type*) [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
variable [CompactSpace R] {ι : Type*}

set_option autoImplicit false

open Filter

variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (F : Ultrafilter ι)


abbrev PatchingModule.Component (α : Ideal R) :=
  UltraProduct (fun i ↦ M i ⧸ (α • ⊤ : Submodule R (M i))) F

variable (M₀ : Type*) [AddCommGroup M₀] [Module R M₀]

open Submodule
def PatchingModule.liftComponent (α : Ideal R) (f : ∀ i, M₀ →ₗ[R] M i) :
    M₀ ⧸ (α • ⊤ : Submodule R M₀) →ₗ[R] Component R M F α :=
  (UltraProduct.πₗ (fun _ ↦ R) _ _).restrictScalars R ∘ₗ LinearMap.pi fun i ↦
    mapQ _ _ (f i) (by rw [← Submodule.map_le_iff_le_comap, map_smul'']; exact Submodule.smul_mono le_rfl le_top)

def OpenIdeals : Type _ := { α : Ideal R // IsOpen (X := R) α }

instance : SemilatticeInf (OpenIdeals R) :=
  Subtype.semilatticeInf fun _ _ ↦ IsOpen.inter

instance : OrderTop (OpenIdeals R) :=
  Subtype.orderTop isOpen_univ

abbrev PatchingModule.componentMap {α β : Ideal R} (h : α ≤ β) : Component R M F α →ₗ[R] Component R M F β :=
  UltraProduct.map (R := fun _ ↦ R)
    (M := (fun i ↦ M i ⧸ (α • ⊤ : Submodule R (M i))))
    (N := (fun i ↦ M i ⧸ (β • ⊤ : Submodule R (M i)))) F
    (fun _ ↦ Submodule.mapQ _ _ LinearMap.id
    (Submodule.smul_mono h le_rfl))

attribute [-instance] instIsScalarTowerUltraProduct in -- needs investigation why this slows everything
def PatchingModule.submodule : Submodule (ι → R) (Π α : OpenIdeals R, Component R M F α.1) where
  carrier := { x | ∀ (α β : OpenIdeals R) (h : α ≤ β), componentMap R M F h (x α) = x β }
  add_mem' {v w} hv hw α β h := by
    dsimp at *
    simp only [map_add, hv α β h, hw α β h]
  zero_mem' := by simp
  smul_mem' c {v} hv α β h := by
    dsimp at *
    simp only [LinearMap.map_smul_of_tower, hv α β h]

omit [IsTopologicalRing R] [CompactSpace R] in
lemma PatchingModule.isClosed_submodule :
    IsClosed (X := Π α : OpenIdeals R, Component R M F α.1) (submodule R M F) := by
  have (α β : OpenIdeals R) (h : α ≤ β) :
      IsClosed { v : Π α : OpenIdeals R, Component R M F α.1 |
        componentMap R M F h (v α) = v β } := by
    exact isClosed_eq (by continuity) (by continuity)
  convert isClosed_iInter fun j ↦ isClosed_iInter fun k ↦ isClosed_iInter (this j k)
  ext; simp; rfl

def PatchingModule : Type _ := PatchingModule.submodule R M F

instance : AddCommGroup (PatchingModule R M F) :=
  inferInstanceAs (AddCommGroup (PatchingModule.submodule R M F))

instance : Module (ι → R) (PatchingModule R M F) :=
  inferInstanceAs (Module (ι → R) (PatchingModule.submodule R M F))

instance : Module R (PatchingModule R M F) :=
  inferInstanceAs (Module R (PatchingModule.submodule R M F))

omit [IsTopologicalRing R] [CompactSpace R] in
@[simp]
lemma PatchingModule.smul_apply (r : R) (x : PatchingModule R M F) (α) :
  (r • x).1 α = r • x.1 α := rfl

instance : IsScalarTower R (ι → R) (PatchingModule R M F) :=
  inferInstanceAs (IsScalarTower R (ι → R) (PatchingModule.submodule R M F))

instance : TopologicalSpace (PatchingModule R M F) :=
  inferInstanceAs (TopologicalSpace (PatchingModule.submodule R M F))

instance : IsTopologicalAddGroup (PatchingModule R M F) :=
  inferInstanceAs (IsTopologicalAddGroup (PatchingModule.submodule R M F))

instance (α : OpenIdeals R) : ContinuousSMul R (PatchingModule.Component R M F α.1) := by
  refine ContinuousSMul.of_nhds_zero (by simp) ?_ (by simp)
  intro x
  obtain ⟨x, rfl⟩ := UltraProduct.πₗ_surjective (fun _ ↦ R) x
  simp only [← LinearMap.map_smul_of_tower, nhds_discrete, pure_zero, tendsto_zero,
    UltraProduct.πₗ_eq_zero, Pi.smul_apply]
  refine eventually_of_mem (α.2.mem_nhds (zero_mem _)) fun a ha ↦ .of_forall fun i ↦ ?_
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (x i)
  rw [← hx, ← Quotient.mk_smul, Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ha trivial

instance : ContinuousSMul R (PatchingModule R M F) :=
  ContinuousSMul.induced ((PatchingModule.submodule R M F).restrictScalars R).subtype

instance : TotallyDisconnectedSpace (PatchingModule R M F) :=
  Subtype.totallyDisconnectedSpace

instance : T2Space (PatchingModule R M F) :=
  inferInstanceAs (T2Space (PatchingModule.submodule R M F))

-- instance : CompactSpace (PatchingModule R M F) :=
--   (IsClosed.isClosedEmbedding_subtypeVal (PatchingModule.isClosed_submodule R M F)).compactSpace

def PatchingModule.π (α : OpenIdeals R) :
    PatchingModule R M F →ₗ[ι → R] PatchingModule.Component R M F α.1 :=
  (LinearMap.proj α) ∘ₗ (PatchingModule.submodule R M F).subtype

def PatchingModule.ofPi :
    (OpenIdeals R → Π i, M i) →ₗ[OpenIdeals R → ι → R]
      Π α : OpenIdeals R, Component R M F α.1 :=
  LinearMap.piMap fun _ ↦ UltraProduct.πₗ _ _ _ ∘ₗ LinearMap.piMap fun _ ↦ Submodule.mkQ _

omit [IsTopologicalRing R] [CompactSpace R] in
@[simp]
lemma PatchingModule.ofPi_apply (x α) :
    ofPi R M F x α = UltraProduct.πₗ (fun _ ↦ R) _ _ fun i ↦ Submodule.Quotient.mk (x α i) := rfl

omit [IsTopologicalRing R] [CompactSpace R] in
variable {R M F} in
lemma PatchingModule.ofPi_surjective :
    Function.Surjective (ofPi R M F) := by
  intro x
  choose y hy using fun a ↦ UltraProduct.πₗ_surjective (fun _ ↦ R) (x a)
  choose z hz using fun i j ↦ Submodule.Quotient.mk_surjective _ (y i j)
  exact ⟨z, by ext; simp [← hy, ← hz]⟩

def PatchingModule.incl :
    (Π i, M i) →ₗ[ι → R] PatchingModule R M F :=
  LinearMap.codRestrict (PatchingModule.submodule R M F)
    ((ofPi R M F).restrictScalars _ ∘ₗ LinearMap.pi fun _ ↦ .id) <| by
  intro v α β h
  rfl

omit [IsTopologicalRing R] [CompactSpace R] in
@[simp]
lemma PatchingModule.incl_apply (x) (α) :
    (PatchingModule.incl R M F x).1 α =
    UltraProduct.πₗ (fun _ ↦ R) (fun i ↦ M i ⧸ (α.1 • ⊤ : Submodule R (M i))) F
      (fun i ↦ Submodule.Quotient.mk (x i)) := rfl

open Module.UniformlyBoundedRank in
instance {α : OpenIdeals R} [Module.UniformlyBoundedRank R M]
    [∀ i, Module.Free (R ⧸ Ann R (M i)) (M i)] :
    Finite (PatchingModule.Component R M F α.1) := by
  let M₁ := fun i ↦ M i ⧸ (α.1 • ⊤ : Submodule R (M i))
  have : Finite (R ⧸ α.1) := AddSubgroup.quotient_finite_of_isOpen _ α.2
  have H₁ := UltraProduct.exists_bijective_of_bddAbove_card (R₀ := R ⧸ α.1) (M := M₁)
    F (Nat.card (R ⧸ α.1) ^ bound R M).succ
    (.of_forall fun i ↦ ⟨Module.UniformlyBoundedRank.finite_quotient_smul R M i α.1,
      (Module.UniformlyBoundedRank.card_quotient_le R M i α.1).trans_lt (Nat.lt_succ_self _)⟩)
  obtain ⟨i, -, hi⟩ := H₁.exists
  have := Module.UniformlyBoundedRank.finite_quotient_smul R M i α.1
  exact (LinearEquiv.ofBijective _ hi).finite_iff.mp inferInstance

variable {M}

section Functorial

variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
variable {N' : ι → Type*} [∀ i, AddCommGroup (N' i)] [∀ i, Module R (N' i)]
variable (f : ∀ i, M i →ₗ[R] N i) (g : ∀ i, N i →ₗ[R] N' i)

abbrev PatchingModule.componentMapModule (α : Ideal R) :
    Component R M F α →ₗ[ι → R] Component R N F α :=
  UltraProduct.map (R := fun _ ↦ R)
    (M := (fun i ↦ M i ⧸ (α • ⊤ : Submodule R (M i))))
    (N := (fun i ↦ N i ⧸ (α • ⊤ : Submodule R (N i)))) F
    (fun _ ↦ Submodule.mapQ _ _ (f _) (by
      simp only [← Submodule.map_le_iff_le_comap, map_smul'', Submodule.map_top]
      exact Submodule.smul_mono le_rfl le_top))

omit [TopologicalSpace R]
  [IsTopologicalRing R]
  [CompactSpace R] in
lemma PatchingModule.componentMapModule_surjective
    (hf : ∀ i, Function.Surjective (f i)) (α : Ideal R) :
    Function.Surjective (componentMapModule R F f α) := by
  apply UltraProduct.map_surjective
  intro i
  rw [← LinearMap.range_eq_top, Submodule.mapQ, Submodule.range_liftQ, LinearMap.range_eq_top]
  exact (Submodule.mkQ_surjective _).comp (hf _)

def PatchingModule.map :
    PatchingModule R M F →ₗ[ι → R] PatchingModule R N F :=
  LinearMap.restrict (p := submodule R M F) (q := submodule R N F)
    ((LinearMap.piMap fun α : OpenIdeals R ↦ componentMapModule R F f α.1).restrictScalars (ι → R))
    (fun x hx α β h ↦ by
      obtain ⟨a, ha⟩ := UltraProduct.πₗ_surjective (fun _ ↦ R) (x α)
      simp only [LinearMap.coe_restrictScalars, LinearMap.piMap_apply,
        ← hx α β h, ← ha, UltraProduct.map_πₗ, LinearMap.coe_restrictScalars, UltraProduct.πₗ_eq_iff]
      filter_upwards with i
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
      rfl)

omit [IsTopologicalRing R] [CompactSpace R] in
@[simp]
lemma PatchingModule.map_apply (x : PatchingModule R M F) (α) :
    (map R F f x).1 α = componentMapModule R F f α.1 (x.1 α) := rfl

omit [IsTopologicalRing R] [CompactSpace R] in
lemma PatchingModule.map_comp_apply (x) :
    map R F (fun i ↦ g i ∘ₗ f i) x = map R F g (map R F f x) := by
  refine Subtype.ext (funext fun α ↦ ?_)
  obtain ⟨y, hy⟩ := ofPi_surjective x.1
  simp [← hy]

omit [IsTopologicalRing R] [CompactSpace R] in
lemma PatchingModule.map_comp :
    map R F (fun i ↦ g i ∘ₗ f i) = map R F g ∘ₗ map R F f :=
  LinearMap.ext (map_comp_apply R F f g)

omit [IsTopologicalRing R] [CompactSpace R] in
@[simp]
lemma PatchingModule.map_id :
    map R F (fun i ↦ .id (M := M i)) = .id := by
  ext x
  refine Subtype.ext (funext fun α ↦ ?_)
  obtain ⟨y, hy⟩ := UltraProduct.πₗ_surjective (fun _ ↦ R) (x.1 α)
  simp [← hy]

@[simps! apply symm_apply]
def PatchingModule.mapEquiv (f : ∀ i, M i ≃ₗ[R] N i) :
    PatchingModule R M F ≃ₗ[ι → R] PatchingModule R N F where
  __ := map R F fun i ↦ (f i).toLinearMap
  invFun := map R F fun i ↦ (f i).symm.toLinearMap
  left_inv x := by simp [← map_comp_apply]
  right_inv x := by simp [← map_comp_apply]

open IsLocalRing in
lemma PatchingModule.map_surjective
    [IsLocalRing R] [IsAdicTopology R]
    [Module.UniformlyBoundedRank R M]
    [∀ i, Module.Free (R ⧸ Ann R (M i)) (M i)]
    (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (map R F f) := by
  intro x
  let s (α : OpenIdeals R) : Set (Component R M F α.1) :=
    componentMapModule R F f α.1 ⁻¹' {x.1 α}
  let fs (α β) (h : α ≤ β) (a : s α) : s β :=
    ⟨componentMap R M F h a.1, by
      obtain ⟨a, ha⟩ := a
      obtain ⟨a, rfl⟩ := UltraProduct.πₗ_surjective (fun _ ↦ R) a
      simp only [LinearMap.coe_restrictScalars, Set.mem_preimage, Set.mem_singleton_iff, s] at ha ⊢
      rw [← x.2 _ _ h, ← ha]
      simp only [UltraProduct.map_πₗ, LinearMap.coe_restrictScalars, UltraProduct.πₗ_eq_iff]
      filter_upwards with i
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (a i)
      simp only [← hb, mapQ_apply, LinearMap.id_coe, id_eq]⟩
  have (α) : Nonempty (s α) := by
    simp only [nonempty_subtype, Set.mem_preimage, Set.mem_singleton_iff, s]
    exact PatchingModule.componentMapModule_surjective R F f hf α.1 (x.1 α)
  obtain ⟨v, hv⟩ := nonempty_inverseLimit_of_finite (s ·) fs (by
      intro i
      ext ⟨a, ha⟩
      obtain ⟨a, rfl⟩ := UltraProduct.πₗ_surjective (fun _ ↦ R) a
      simp only [LinearMap.coe_restrictScalars, mapQ_id,
        UltraProduct.map_πₗ, LinearMap.id_coe, id_eq, fs]) (by
      intro i j k hij hjk
      ext ⟨a, ha⟩
      obtain ⟨a, rfl⟩ := UltraProduct.πₗ_surjective (fun _ ↦ R) a
      simp only [Function.comp_apply, LinearMap.coe_restrictScalars,
        UltraProduct.map_πₗ, UltraProduct.πₗ_eq_iff, fs]
      filter_upwards with i
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (a i)
      simp only [← hb, mapQ_apply, LinearMap.id_coe, id_eq])
    (l := fun k ↦ ⟨maximalIdeal R ^ k, isOpen_maximalIdeal_pow R k⟩)
    (fun i j ↦ Ideal.pow_le_pow_right)
    (fun α ↦ have : Finite (R ⧸ α.1) := AddSubgroup.quotient_finite_of_isOpen _ α.2
      exists_maximalIdeal_pow_le_of_finite_quotient _)
  refine ⟨⟨fun i ↦ (v i).1, fun α β h ↦ congr_arg Subtype.val (hv α β h)⟩, ?_⟩
  refine Subtype.ext (funext fun α ↦ ?_)
  have : _ = _ := (v α).2
  simpa using this

end Functorial

def PatchingModule.toConst (M) [AddCommGroup M] [Module R M] :
    M →ₗ[R] PatchingModule R (fun _ ↦ M) F :=
  (incl R (fun _ ↦ M) F).restrictScalars R ∘ₗ .pi fun _ ↦ .id

lemma PatchingModule.toConst_surjective (M) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (toConst R F M) := by
  letI := moduleTopology R M
  have : IsModuleTopology R M := ⟨rfl⟩
  have : CompactSpace M := IsModuleTopology.compactSpace R M
  have H : Continuous (toConst R F M) := by
    exact IsModuleTopology.continuous_of_linearMap _
  suffices DenseRange (toConst R F M) by
    rw [← Set.range_eq_univ, ← this.closure_eq,
      (isCompact_range H).isClosed.closure_eq]
  refine denseRange_inverseLimit (ι := OpenIdeals R) _ _
    (fun _ _ _ ↦ continuous_of_discreteTopology) _
    fun α ↦ denseRange_discrete.mpr ?_
  suffices Function.Surjective (liftComponent R (fun _ ↦ M) F M _ (fun _ ↦ .id)) by
    exact this.comp (Submodule.Quotient.mk_surjective _)
  have : Finite (M ⧸ (α.1 • ⊤ : Submodule R M)) := by
    have : Finite (R ⧸ α.1) := AddSubgroup.quotient_finite_of_isOpen _ α.2
    have : Module.Finite (R ⧸ α.1) (M ⧸ (α.1 • ⊤ : Submodule R M)) :=
      .of_restrictScalars_finite R _ _
    exact Module.finite_of_finite (R ⧸ α.1)
  apply UltraProduct.surjective_of_eventually_surjective
  filter_upwards with i
  rw [← LinearMap.range_eq_top, mapQ, range_liftQ, LinearMap.range_eq_top]
  exact Submodule.mkQ_surjective _

noncomputable
def PatchingModule.constEquiv [IsLocalRing R] [T2Space R] [IsNoetherianRing R]
    (M) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    M ≃ₗ[R] PatchingModule R (fun _ ↦ M) F := by
  refine .ofBijective (toConst R F M) ⟨?_, toConst_surjective R F M⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : ∀ α : OpenIdeals R, a ∈ α.1 • (⊤ : Submodule R M) := by
    simpa [toConst, incl_apply] using congr_fun (congr_arg Subtype.val ha)
  rw [← Submodule.mem_bot (R := R), ← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top, Submodule.mem_iInf]
  intro i
  exact this ⟨_, IsLocalRing.isOpen_maximalIdeal_pow' R i⟩

variable (M)

class IsPatchingSystem (F : Filter ι) : Prop where
  cond : ∀ α : Ideal R, IsOpen (X := R) α → ∀ᶠ i in F, Ann R (M i) ≤ α

variable [∀ i, Module.Free (R ⧸ Ann R (M i)) (M i)]
variable [Module.UniformlyBoundedRank R M] [IsPatchingSystem R M F]

open Module.UniformlyBoundedRank

noncomputable
def IsPatchingSystem.linearMap (α : Ideal R) (i) :
    (Fin (rank R M F) → R ⧸ α) →ₗ[R] M i ⧸ (α • ⊤ : Submodule R (M i)) :=
  Pi.liftQuotientₗ (Module.UniformlyBoundedRank.linearMap R M F i) _

omit [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [IsPatchingSystem R M F] in
lemma IsPatchingSystem.linearMap_compLeft (α : Ideal R) (i) (x) :
    linearMap R M F α i ((Algebra.linearMap R (R ⧸ α)).compLeft _ x) =
      Submodule.Quotient.mk (Module.UniformlyBoundedRank.linearMap R M F i x) := by
  simp [linearMap, LinearMap.quotKerEquivOfSurjective, LinearEquiv.ofTop_symm_apply, Pi.liftQuotientₗ]

omit [IsTopologicalRing R] [CompactSpace R] in
lemma IsPatchingSystem.linearMap_bijective (α : Ideal R) (hα : IsOpen (X := R) α) :
    ∀ᶠ i in F, Function.Bijective (linearMap R M F α i) := by
  filter_upwards [linearMap_surjective R M F,
    linearMap_eq_zero R M F,
    IsPatchingSystem.cond (M := M) (F := F) α hα] with i h₁ h₂ h₃
  refine Pi.liftQuotientₗ_bijective _ _ h₁ fun x hx ↦ ?_
  simpa [funext_iff, Ideal.Quotient.eq_zero_iff_mem] using fun i ↦ h₃ ((h₂ _).mp hx i)

noncomputable
def PatchingModule.equivComponent (α : Ideal R) (hα : IsOpen (X := R) α) :
    (Fin (rank R M F) → R ⧸ α) ≃ₗ[R] Component R M F α :=
  haveI : Finite (R ⧸ α) := AddSubgroup.quotient_finite_of_isOpen _ hα
  LinearEquiv.ofBijective _ (UltraProduct.bijective_of_eventually_bijective
    (IsPatchingSystem.linearMap R M F α) F
    (IsPatchingSystem.linearMap_bijective R M F α hα))

noncomputable
def PatchingModule.mapOfIsPatchingSystem :
    (Fin (rank R M F) → R) →ₗ[R] PatchingModule R M F :=
  LinearMap.codRestrict
    ((submodule R M F).restrictScalars R)
    (LinearMap.pi fun α ↦ (equivComponent R M F α.1 α.2).toLinearMap ∘ₗ
      (Algebra.linearMap _ _).compLeft _) fun c α β hαβ ↦ by
    simp [equivComponent, IsPatchingSystem.linearMap_compLeft]

lemma PatchingModule.continuous_ofPi : Continuous (mapOfIsPatchingSystem R M F) := by
  refine continuous_induced_rng.mpr ?_
  refine continuous_pi fun α ↦ ?_
  have : DiscreteTopology (R ⧸ α.1) := AddSubgroup.discreteTopology _ α.2
  show Continuous ((equivComponent R M F α.1 α.2) ∘ _)
  refine continuous_of_discreteTopology.comp ?_
  refine continuous_pi fun i ↦
    (continuous_algebraMap R (R ⧸ α.1)).comp (continuous_apply i)

-- Compact + T2 actually implies NonarchimedeanRing.
variable [NonarchimedeanRing R] [T2Space R]

noncomputable
def PatchingModule.mapOfIsPatchingSystem_bijective :
    Function.Bijective (mapOfIsPatchingSystem R M F) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    ext i
    replace hx : ∀ α : OpenIdeals R, equivComponent R M F α.1 α.2 _ = 0 :=
      funext_iff.mp (congr_arg Subtype.val hx)
    replace hx : ∀ α : OpenIdeals R, ∀ i, x i ∈ α.1 := by
      simpa [funext_iff, Ideal.Quotient.eq_zero_iff_mem] using hx
    by_contra hx'
    obtain ⟨U, hU, h0U, hxU⟩ := t1Space_iff_exists_open.mp (inferInstanceAs (T1Space R)) (.symm hx')
    obtain ⟨I, hI, hIU⟩ := exists_ideal_isOpen_and_subset (hU.mem_nhds h0U)
    exact hxU (hIU (hx ⟨I, hI⟩ i))
  · suffices DenseRange (mapOfIsPatchingSystem R M F) by
      rw [← Set.range_eq_univ, ← this.closure_eq,
        (isCompact_range (continuous_ofPi R M F)).isClosed.closure_eq]
    refine denseRange_inverseLimit (ι := OpenIdeals R) _ _
      (fun _ _ _ ↦ continuous_of_discreteTopology) _
      fun α ↦ denseRange_discrete.mpr ?_
    exact (equivComponent R M F α.1 α.2).surjective.comp
      (Function.Surjective.comp_left Ideal.Quotient.mk_surjective)

instance : Module.Free R (PatchingModule R M F) :=
  .of_equiv (LinearEquiv.ofBijective _ (PatchingModule.mapOfIsPatchingSystem_bijective R M F))

instance : Module.Finite R (PatchingModule R M F) :=
  .of_surjective _ (PatchingModule.mapOfIsPatchingSystem_bijective R M F).surjective

lemma PatchingModule.rank_patchingModule [Nontrivial R] :
    Module.rank R (PatchingModule R M F) = rank R M F := by
  simpa using LinearEquiv.lift_rank_eq
    (LinearEquiv.ofBijective _ (PatchingModule.mapOfIsPatchingSystem_bijective R M F)).symm
#min_imports
