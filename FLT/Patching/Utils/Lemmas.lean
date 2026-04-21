module

public import Mathlib.RingTheory.Filtration
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.RingTheory.Spectrum.Prime.Basic

@[expose] public section


lemma IsUnit.pi_iff {ι} {M : ι → Type*} [∀ i, Monoid (M i)] {x : Π i, M i} :
    IsUnit x ↔ ∀ i, IsUnit (x i) := by
  simp_rw [isUnit_iff_exists, funext_iff, ← forall_and]
  exact Classical.skolem (p := fun i y ↦ x i * y = 1 ∧ y * x i = 1).symm

lemma forall_prod_iff {ι} {β : ι → Type*} (P : ∀ i, β i → Prop) [∀ i, Nonempty (β i)] :
    (∀ i : ι, ∀ (y : Π i, β i), P i (y i)) ↔ (∀ i y, P i y) :=
  letI := Classical.decEq
  ⟨fun H i y ↦ by simpa using H i (fun j ↦ if h : i = j then h ▸ y else
    Nonempty.some inferInstance), fun H i y ↦ H _ _⟩

@[simps]
def Ideal.idealQuotientEquiv {R : Type*} [CommRing R] (I : Ideal R) :
  Ideal (R ⧸ I) ≃ { J // I ≤ J } where
    toFun J := ⟨J.comap (Ideal.Quotient.mk I),
      (I.mk_ker : _).symm.trans_le (Ideal.comap_mono bot_le)⟩
    invFun J := J.1.map (Ideal.Quotient.mk I)
    left_inv J := map_comap_of_surjective _ Quotient.mk_surjective _
    right_inv J := by
      ext1
      simpa [comap_map_of_surjective _ Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot] using J.2

set_option autoImplicit false
variable {ι : Type*} {R M : ι → Type*} [∀ i, CommRing (R i)] [∀ i, AddCommGroup (M i)]
variable [∀ i, Module (R i) (M i)]
variable (I : ∀ i, Ideal (R i)) (N : ∀ i, Submodule (R i) (M i))

def Submodule.pi' : Submodule (Π i, R i) (Π i, M i) where
  carrier := { x | ∀ i, x i ∈ N i }
  add_mem' := by aesop
  zero_mem' := by aesop
  smul_mem' := by aesop

variable {N} in
@[simp]
lemma Submodule.mem_pi' {x} : x ∈ Submodule.pi' N ↔ ∀ i, x i ∈ N i := Iff.rfl

variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module (R i) (N i)] in
/-- A more dependent version of `LinearMap.piMap`, making a product of linear maps
into a linear map over the product of rings. -/
@[simps]
def LinearMap.piMap' (f : ∀ i, M i →ₗ[R i] N i) : (Π i, M i) →ₗ[Π i, R i] Π i, N i where
  toFun g i := f i (g i)
  map_add' := by aesop
  map_smul' := by aesop

instance {ι : Type*} {R A : ι → Type*} [∀ i, CommSemiring (R i)]
    [∀ i, Semiring (A i)] [∀ i, Algebra (R i) (A i)] : Algebra (Π i, R i) (Π i, A i) where
  algebraMap := Pi.ringHom fun i ↦ (algebraMap (R i) (A i)).comp (Pi.evalRingHom R i)
  commutes' r a := funext fun i ↦ Algebra.commutes _ _
  smul_def' r a := funext fun i ↦ by simp [Algebra.smul_def]

lemma pi'_jacobson :
    Submodule.pi' (fun i ↦ Ideal.jacobson (R := R i) ⊥) = Ideal.jacobson ⊥ := by
  ext v
  simp only [Submodule.mem_pi', Ideal.mem_jacobson_bot, IsUnit.pi_iff]
  conv_rhs => rw [forall_comm]
  exact (forall_prod_iff (fun i y ↦ IsUnit (v i * y + 1))).symm

instance {R} [CommRing R] [TopologicalSpace R] [CompactSpace R] (I : Ideal R) :
    CompactSpace (R ⧸ I) :=
  Quotient.compactSpace

open Topology in
@[to_additive]
theorem exists_subgroup_isOpen_and_subset {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [T2Space α] [TotallyDisconnectedSpace α]
    [CommGroup α] [IsTopologicalGroup α] {U : Set α} (hU : U ∈ 𝓝 1) :
    ∃ G : Subgroup α, IsOpen (X := α) G ∧ (G : Set α) ⊆ U := by
  obtain ⟨V, hVU, hV, h1V⟩ := mem_nhds_iff.mp hU
  obtain ⟨K, hK, hxK, hKU⟩ := compact_exists_isClopen_in_isOpen hV h1V
  obtain ⟨⟨G, hG⟩, hG'⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hK hxK
  exact ⟨G, hG, (hG'.trans hKU).trans hVU⟩

@[simp]
theorem TwoSidedIdeal.span_le' {α} [NonUnitalNonAssocRing α] {s : Set α} {I : TwoSidedIdeal α} :
    span s ≤ I ↔ s ⊆ I :=
  ⟨subset_span.trans, fun h _ hx ↦ mem_span_iff.mp hx I h⟩

@[simp]
theorem TwoSidedIdeal.span_neg {α} [NonUnitalNonAssocRing α] (s : Set α) :
    TwoSidedIdeal.span (-s) = TwoSidedIdeal.span s := by
  apply le_antisymm <;> rw [span_le']
  · rintro x hx
    exact neg_neg x ▸ neg_mem _ (subset_span (s := s) hx)
  · rintro x hx
    exact neg_neg x ▸ neg_mem _ (subset_span (Set.neg_mem_neg.mpr hx))

@[simp]
theorem TwoSidedIdeal.span_singleton_zero {α} [NonUnitalNonAssocRing α] :
    span {(0 : α)} = ⊥ :=
  le_bot_iff.mp (span_le'.mpr (by simp))

theorem TwoSidedIdeal.mem_span_singleton {α} [NonUnitalNonAssocRing α] {x : α} :
    x ∈ span {x} :=
  subset_span rfl

def TwoSidedIdeal.leAddSubgroup {α} [NonUnitalNonAssocRing α] (G : AddSubgroup α) :
    TwoSidedIdeal α :=
  .mk'
    { x | (span {x} : Set α) ⊆ G }
    -- TODO: `TwoSidedIdeal.span` shouldn't be an `abbrev`!!
    (by simp [-coe_mk, G.zero_mem])
    (fun {x y} hx hy ↦ by
      have : span {x + y} ≤ span {x} ⊔ span {y} :=
        span_le'.mpr <| Set.singleton_subset_iff.mpr <|
          mem_sup.mpr ⟨x, mem_span_singleton, y, mem_span_singleton, rfl⟩
      refine subset_trans (c := (G : Set α)) this fun a ha ↦ ?_
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup.mp ha
      exact G.add_mem (hx ha₁) (hy ha₂))
    (fun {x} hx ↦ by simpa only [Set.mem_setOf_eq, ← Set.neg_singleton, TwoSidedIdeal.span_neg])
    (fun {x y} hy ↦ subset_trans (c := (G : Set α))
      (TwoSidedIdeal.span_le'.mpr <| by
        simpa using TwoSidedIdeal.mul_mem_left _ x y mem_span_singleton) hy)
    (fun {x y} hy ↦ subset_trans (c := (G : Set α))
      (TwoSidedIdeal.span_le'.mpr <| by
        simpa using TwoSidedIdeal.mul_mem_right _ x y mem_span_singleton) hy)

lemma TwoSidedIdeal.leAddSubgroup_subset {α} [NonUnitalNonAssocRing α] (G : AddSubgroup α) :
    (leAddSubgroup G : Set α) ⊆ G :=
  fun x hx ↦ hx ((sub_zero x).symm ▸ mem_span_singleton)

lemma TwoSidedIdeal.mem_leAddSubgroup' {α} [NonUnitalNonAssocRing α] {G : AddSubgroup α} {x : α} :
    x ∈ leAddSubgroup G ↔ (span {x} : Set α) ⊆ G := by
  conv_rhs => rw [← sub_zero x]
  rfl

lemma TwoSidedIdeal.mem_leAddSubgroup {α} [Ring α] {G : AddSubgroup α} {x : α} :
    x ∈ leAddSubgroup G ↔ ∀ a b, a * x * b ∈ G := by
  constructor
  · intro hx a b
    exact hx (mul_mem_right _ _ _ (mul_mem_left _ _ _ ((sub_zero x).symm ▸ mem_span_singleton)))
  · intro H a ha
    simpa using mem_span_iff.mp ha (.mk' { x | ∀ a b, a * x * b ∈ G }
      (by simp [G.zero_mem]) (by simp +contextual [mul_add, add_mul, G.add_mem])
      (by simp) (fun {x y} ↦ by simp +contextual [← mul_assoc _ x y])
      (fun {x y} ↦ by simp +contextual [mul_assoc])) (by simpa) 1 1

open Topology Pointwise in
theorem exists_twoSidedIdeal_isOpen_and_subset {α} [TopologicalSpace α]
    [CompactSpace α] [T2Space α] [TotallyDisconnectedSpace α]
    [Ring α] [IsTopologicalRing α] {U : Set α} (hU : U ∈ 𝓝 0) :
    ∃ I : TwoSidedIdeal α, IsOpen (X := α) I ∧ (I : Set α) ⊆ U := by
  obtain ⟨G, hG, hGU⟩ := exists_addSubgroup_isOpen_and_subset hU
  refine ⟨_, isOpen_iff_mem_nhds.mpr ?_, (TwoSidedIdeal.leAddSubgroup_subset G).trans hGU⟩
  intro x hx
  replace hx := TwoSidedIdeal.mem_leAddSubgroup.mp hx
  suffices
    ∀ s t, IsCompact s → IsCompact t →
      ∃ V ∈ 𝓝 x, ∀ a ∈ s, ∀ b ∈ V, ∀ c ∈ t, a * b * c ∈ G by
    obtain ⟨V, hV, H⟩ := this Set.univ Set.univ isCompact_univ isCompact_univ
    refine (𝓝 x).mem_of_superset hV fun b hb ↦ ?_
    replace H := fun a c ↦ H a trivial b hb c trivial
    simpa [TwoSidedIdeal.mem_leAddSubgroup]
  intros s t hs ht
  refine hs.induction_on ?_ ?_ ?_ ?_
  · simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨Set.univ, Filter.univ_mem⟩
  · rintro s₁ s₂ hs₁s₂ ⟨V, hV, H⟩
    exact ⟨V, hV, fun a ha b hb c hc ↦ H a (hs₁s₂ ha) b hb c hc⟩
  · rintro s₁ s₂ ⟨V₁, hV₁, H₁⟩ ⟨V₂, hV₂, H₂⟩
    exact ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂,
      fun a ha b hb c hc ↦ ha.elim (H₁ a · b hb.1 c hc) (H₂ a · b hb.2 c hc)⟩
  intro a has
  refine ht.induction_on ?_ ?_ ?_ ?_
  · simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true, and_true,
      exists_and_right]
    exact ⟨⟨_, Filter.univ_mem⟩, ⟨_, Filter.univ_mem⟩⟩
  · rintro s₁ s₂ hs₁s₂ ⟨V, hV, U, hU, H⟩
    exact ⟨V, hV, U, hU, fun a ha b hb c hc ↦ H a ha b hb c (hs₁s₂ hc)⟩
  · rintro s₁ s₂ ⟨V₁, hV₁, U₁, hU₁, H₁⟩ ⟨V₂, hV₂, U₂, hU₂, H₂⟩
    exact ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂, U₁ ∩ U₂, Filter.inter_mem hU₁ hU₂,
      fun a ha b hb c hc ↦ hc.elim (H₁ a ha.1 b hb.1 c) (H₂ a ha.2 b hb.2 c)⟩
  · intros b hbt
    have : Continuous fun p : α × α × α ↦ p.1 * p.2.1 * p.2.2 := by fun_prop
    have := (this.tendsto (a, x, b)) (hG.mem_nhds (hx _ _))
    simp only [nhds_prod_eq, Filter.mem_map, Filter.mem_prod_iff] at this
    obtain ⟨t₁, ht₁, T, ⟨t₂, ht₂, t₃, ht₃, hT⟩, H⟩ := this
    refine ⟨t₃, mem_nhdsWithin_of_mem_nhds ht₃, t₁, mem_nhdsWithin_of_mem_nhds ht₁,
      t₂, ht₂, fun a ha b hb c hc ↦ ?_⟩
    exact H (Set.mk_mem_prod ha (hT <| Set.mk_mem_prod hb hc))

open Topology in
theorem exists_ideal_isOpen_and_subset {α} [TopologicalSpace α]
    [CompactSpace α] [T2Space α] [TotallyDisconnectedSpace α]
    [Ring α] [IsTopologicalRing α] {U : Set α} (hU : U ∈ 𝓝 0) :
    ∃ I : Ideal α, IsOpen (X := α) I ∧ (I : Set α) ⊆ U := by
  obtain ⟨I, hI, hIU⟩ := exists_twoSidedIdeal_isOpen_and_subset hU
  exact ⟨I.asIdeal, hI, hIU⟩

instance (priority := 100) {α} [TopologicalSpace α] [DiscreteTopology α] :
    TotallyDisconnectedSpace α :=
  ⟨fun s _ hs x hxs y hys ↦ not_not.mp fun hxy ↦ by
    simpa using hs _ _ (isOpen_discrete {y}) (isOpen_discrete (s \ {y}))
      (by simp) ⟨y, by simpa⟩ ⟨x, by simp_all⟩⟩

lemma WellFoundedGT.exists_eq_sup {α} [CompleteLattice α] [WellFoundedGT α]
    (f : ℕ →o α) : ∃ i, f i = ⨆ i, f i := by
  obtain ⟨n, hn⟩ := wellFoundedGT_iff_monotone_chain_condition.mp ‹WellFoundedGT α› f
  exact ⟨n, le_antisymm (le_iSup _ _) (iSup_le fun i ↦
    (le_total i n).elim (f.2 ·) (fun h ↦ (hn _ h).ge))⟩

lemma WellFoundedLT.exists_eq_inf {α} [CompleteLattice α] [WellFoundedLT α]
    (f : ℕ →o αᵒᵈ) : ∃ i, f i = (⨅ i, f i : α) :=
  WellFoundedGT.exists_eq_sup (α := αᵒᵈ) f

lemma IsLocalRing.maximalIdeal_pow_card_smul_top_le {R M}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Finite (M ⧸ N)] : maximalIdeal R ^ Nat.card (M ⧸ N) • ⊤ ≤ N := by
  let f (n) : Submodule R (M ⧸ N) := maximalIdeal R ^ n • ⊤
  have hf : ∀ i j, i ≤ j → f j ≤ f i :=
    fun i j h ↦ Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl
  have H : ∃ i, f i = ⊥ := by
    obtain ⟨i, hi⟩ := WellFoundedLT.exists_eq_inf ⟨f, hf⟩
    have := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := R) (M := M ⧸ N) _
      (maximalIdeal.isMaximal R).ne_top
    exact ⟨i, by simpa [f, this] using hi⟩
  have (i : ℕ) : Set.ncard (α := M ⧸ N) (f i) ≤ Nat.card (M ⧸ N) - i + 1 := by
    induction i with
    | zero =>
      refine (Set.ncard_mono (Set.subset_univ _)).trans ?_
      simp [Set.ncard_univ]
    | succ n IH =>
      cases (hf _ _ n.le_succ).lt_or_eq with
      | inl h =>
        rw [← tsub_tsub]
        refine (Nat.le_sub_one_of_lt <| (Set.ncard_strictMono h).trans_le IH).trans ?_
        omega
      | inr h =>
        have (i : ℕ) : f (i + n) = f n := by
          induction i with
          | zero => simp
          | succ m IH =>
            unfold f at *
            simp only [add_assoc, pow_add _ m, mul_smul, ← Nat.succ_eq_one_add, h]
            simp only [← mul_smul, ← pow_add, IH]
        obtain ⟨i, hi⟩ := H
        replace hf := hf _ _ (i.le_add_right n)
        rw [this, hi, ← h, le_bot_iff] at hf
        simp [hf]
  have : f (Nat.card (M ⧸ N)) = ⊥ := by
    rw [← le_bot_iff]
    change (f (Nat.card (M ⧸ N)) : Set (M ⧸ N)) ⊆ {0}
    exact (Set.eq_of_subset_of_ncard_le (by simp) ((this _).trans (by simp))).ge
  simpa only [f, ← LinearMap.range_eq_top.mpr N.mkQ_surjective, ← Submodule.map_top,
    ← Submodule.map_smul'', ← le_bot_iff, Submodule.map_le_iff_le_comap, Submodule.comap_bot,
    Submodule.ker_mkQ] using this

theorem Submodule.comap_smul_of_le_range {R M M'} [CommRing R] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') (S : Submodule R M') (hS : S ≤ LinearMap.range f) (I : Ideal R) :
    (I • S).comap f = (I • S.comap f) ⊔ LinearMap.ker f := by
  rw [← comap_map_eq, map_smul'', Submodule.map_comap_eq, inf_eq_right.mpr hS]

theorem Submodule.comap_smul_of_surjective {R M M'} [CommRing R] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') (S : Submodule R M') (hS : Function.Surjective f) (I : Ideal R) :
    (I • S).comap f = (I • S.comap f) ⊔ LinearMap.ker f :=
  comap_smul_of_le_range f S (le_top.trans_eq (LinearMap.range_eq_top_of_surjective f hS).symm) I

noncomputable
def Pi.liftQuotientₗ {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]
    (f : (ι → R) →ₗ[R] M) (I : Ideal R) : (ι → R ⧸ I) →ₗ[R] M ⧸ (I • ⊤ : Submodule R M) := by
  refine Submodule.liftQ _ (Submodule.mkQ _ ∘ₗ f) ?_ ∘ₗ
    (((Algebra.linearMap R (R ⧸ I)).compLeft ι).quotKerEquivOfSurjective ?_).symm.toLinearMap
  · intro x hx
    replace hx : ∀ i, x i ∈ I := by
      simpa [funext_iff, Ideal.Quotient.eq_zero_iff_mem] using hx
    cases nonempty_fintype ι
    classical
    have : x = ∑ i : ι, x i • (Pi.single i 1 : ι → R) := by
      simp [← Pi.single_smul, Finset.univ_sum_single]
    rw [this]
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    simp only [map_sum, map_smul]
    exact sum_mem fun i hi ↦ Submodule.smul_mem_smul (hx i) Submodule.mem_top
  · exact Function.Surjective.comp_left Ideal.Quotient.mk_surjective

lemma Pi.liftQuotientₗ_surjective {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite ι] (f : (ι → R) →ₗ[R] M) (I : Ideal R) (hf : Function.Surjective f) :
    Function.Surjective (Pi.liftQuotientₗ f I) := by
  simp only [liftQuotientₗ, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.surjective_comp]
  rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
  exact (Submodule.mkQ_surjective _).comp hf

lemma Pi.liftQuotientₗ_bijective {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite ι] (f : (ι → R) →ₗ[R] M) (I : Ideal R) (hf : Function.Surjective f)
    (hf' : LinearMap.ker f ≤ LinearMap.ker ((Algebra.linearMap R (R ⧸ I)).compLeft ι)) :
    Function.Bijective (Pi.liftQuotientₗ f I) := by
  refine ⟨?_, liftQuotientₗ_surjective f I hf⟩
  simp only [liftQuotientₗ, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp]
  rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, ← le_bot_iff, Submodule.map_le_iff_le_comap,
      Submodule.comap_bot, Submodule.ker_mkQ, LinearMap.ker_comp, Submodule.ker_mkQ,
      Submodule.comap_smul_of_surjective _ _ hf, Submodule.comap_top]
  refine sup_le (Submodule.smul_le.mpr ?_) hf'
  rintro r hr m -
  simp only [LinearMap.mem_ker, funext_iff, LinearMap.compLeft_apply, Function.comp_apply,
    smul_apply, Algebra.linearMap_apply, Ideal.Quotient.algebraMap_eq, zero_apply,
    Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul, I.mul_mem_right _ hr, implies_true]

lemma IsModuleTopology.compactSpace
    (R M : Type*) [CommRing R] [TopologicalSpace R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
    [CompactSpace R] [Module.Finite R M] : CompactSpace M :=
  letI : ContinuousAdd M := toContinuousAdd R M
  ⟨Submodule.isCompact_of_fg (Module.Finite.fg_top (R := R))⟩

lemma disjoint_nonZeroDivisors_of_mem_minimalPrimes
    {R : Type*} [CommRing R] (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    Disjoint (p : Set R) (nonZeroDivisors R) := by
  classical
  rw [← Set.subset_compl_iff_disjoint_right, Set.subset_def]
  simp only [SetLike.mem_coe, Set.mem_compl_iff, mem_nonZeroDivisors_iff_right, not_forall]
  intro x hxp
  have := hp.1.1
  have : p.map (algebraMap R (Localization.AtPrime p)) ≤ nilradical _ := by
    rw [nilradical, Ideal.radical_eq_sInf, le_sInf_iff]
    rintro q ⟨-, hq⟩
    obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
    rw [Ideal.map_le_iff_le_comap]
    exact hp.2 ⟨h₁, bot_le⟩ h₂
  obtain ⟨n, hn : _ = 0⟩ := this (Ideal.mem_map_of_mem _ hxp)
  rw [← map_pow, ← map_zero (algebraMap R _), IsLocalization.eq_iff_exists p.primeCompl] at hn
  obtain ⟨t, ht⟩ := hn
  simp only [mul_zero] at ht
  have H : ∃ n, t.1 * x ^ n = 0 := ⟨n, ht⟩
  have : Nat.find H ≠ 0 := by
    intro h
    have := Nat.find_spec H
    simp only [h, pow_zero, mul_one] at this
    exact t.2 (this ▸ zero_mem p)
  refine ⟨t.1 * x ^ (Nat.find H - 1), ?_, ?_⟩
  · rw [mul_assoc, ← pow_succ, tsub_add_cancel_of_le, Nat.find_spec H]
    rwa [Nat.one_le_iff_ne_zero]
  · exact Nat.find_min H (Nat.sub_one_lt this)
