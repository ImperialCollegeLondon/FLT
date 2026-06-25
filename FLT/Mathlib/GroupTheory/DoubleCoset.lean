/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, Kevin Buzzard, Andrew Yang
-/
module

public import FLT.AutomorphicForm.GroupTheoryStuff
public import FLT.Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Double Coset

Material destined for Mathlib.
-/

@[expose] public section

theorem DoubleCoset.isOpen_doubleCoset {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : DoubleCoset.Quotient H K) :
    IsOpen (X := G) (doubleCoset (Quotient.out i) H K) := by
  simpa only [doubleCoset] using (IsOpen.mul_left hK)

lemma DoubleCoset.mk_surjective {G : Type*} [Group G] (H K : Subgroup G) :
    Function.Surjective (DoubleCoset.mk H K) := Quotient.mk_surjective

theorem DoubleCoset.isOpen_doubleCoset_rightrel_mk {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : DoubleCoset.Quotient H K) :
    IsOpen (Quot.mk ⇑(QuotientGroup.rightRel H) '' doubleCoset (Quotient.out i) H K) := by
  apply (QuotientGroup.isOpenQuotientMap_rightrel_mk H).isOpenMap
  exact DoubleCoset.isOpen_doubleCoset H K hK i

def DoubleCoset.map {G₁ G₂ : Type*} [Group G₁] [Group G₂] (H₁ K₁ : Subgroup G₁)
    (H₂ K₂ : Subgroup G₂) (e : G₁ →* G₂) (eH : H₁ ≤ H₂.comap e) (eK : K₁ ≤ K₂.comap e) :
    DoubleCoset.Quotient (G := G₁) H₁ K₁ → DoubleCoset.Quotient (G := G₂) H₂ K₂ :=
  Quotient.map e fun a b H ↦ by
    simp only [DoubleCoset.rel_iff] at H ⊢
    obtain ⟨x, hx, y, hy, rfl⟩ := H
    refine ⟨e x, eH hx, e y, eK hy, by simp⟩

@[simp]
lemma DoubleCoset.map_mk {G₁ G₂ : Type*} [Group G₁] [Group G₂] (H₁ K₁ : Subgroup G₁)
    (H₂ K₂ : Subgroup G₂) (e : G₁ →* G₂) (eH : H₁ ≤ H₂.comap e) (eK : K₁ ≤ K₂.comap e) (x) :
    map H₁ K₁ H₂ K₂ e eH eK (DoubleCoset.mk _ _ x) = DoubleCoset.mk _ _ (e x) := rfl

def DoubleCoset.quotientEquiv {G₁ G₂ : Type*} [Group G₁] [Group G₂] (H₁ K₁ : Set G₁)
    (H₂ K₂ : Set G₂) (e : G₁ ≃* G₂) (eH : e ⁻¹' H₂ = H₁) (eK : e ⁻¹' K₂ = K₁) :
    DoubleCoset.Quotient H₁ K₁ ≃ DoubleCoset.Quotient H₂ K₂ :=
  Quotient.congr e fun x y ↦ by
    simp [← (Set.image_injective.mpr e.injective).eq_iff, DoubleCoset.doubleCoset_eq_image2,
      Set.image_image2, Set.image2_image_left, Set.image2_image_right,
      (Equiv.preimage_eq_iff_eq_image ..).mp eH, (Equiv.preimage_eq_iff_eq_image ..).mp eK]

@[simp]
lemma DoubleCoset.quotientEquiv_mk {G₁ G₂ : Type*} [Group G₁] [Group G₂] (H₁ K₁ : Subgroup G₁)
    (H₂ K₂ : Subgroup G₂) (e : G₁ ≃* G₂) (eH : e ⁻¹' H₂ = H₁) (eK : e ⁻¹' K₂ = K₁) (x) :
    quotientEquiv H₁ K₁ H₂ K₂ e eH eK (DoubleCoset.mk _ _ x) = DoubleCoset.mk _ _ (e x) := rfl

open scoped Pointwise in
lemma Set.mul_right_singleton_bijective
    {G : Type*} [Group G] (g : G) : Function.Bijective (· * ({g} : Set G)) := by
  convert (Group.isUnit (MulOpposite.op g)).smul_bijective (β := Set G) using 1
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem]

open scoped Pointwise in
def DoubleCoset.mulRightEquiv {G : Type*} [Group G] (H K gK : Set G) (g : G)
    (hgK : gK = ConjAct.toConjAct g⁻¹ • K) :
    DoubleCoset.Quotient H K ≃ DoubleCoset.Quotient H gK :=
  Quotient.congr (Equiv.mulRight g) fun x y ↦ by
    have : {g} * gK = K * {g} := by
      rw [hgK]; ext; simp [Set.mem_inv_smul_set_iff, ConjAct.toConjAct_smul, mul_assoc]
    simp only [Setoid.ker_def, Equiv.coe_mulRight, doubleCoset,
      ← Set.singleton_mul_singleton, mul_assoc, this]
    rw [← (Set.mul_right_singleton_bijective g).injective.eq_iff]
    simp only [mul_assoc]

open scoped Pointwise in
@[simp]
lemma DoubleCoset.mulRightEquiv_mk {G : Type*} [Group G] (H K gK : Subgroup G) (g : G)
    (hgK) (a : G) :
    mulRightEquiv H K gK g hgK (DoubleCoset.mk _ _ a) = DoubleCoset.mk _ _ (a * g) := rfl

open scoped Pointwise in
@[simp]
lemma DoubleCoset.mulRightEquiv_symm_mk {G : Type*} [Group G] (H K gK : Subgroup G) (g : G)
    (hgK) (a : G) :
    (mulRightEquiv H K gK g hgK).symm (DoubleCoset.mk _ _ a) = DoubleCoset.mk _ _ (a * g⁻¹) := rfl

variable {G : Type*} [Group G] (H K : Subgroup G)

local notation H "＼" G "／" K:max => DoubleCoset.Quotient (G := G) H K
local notation H "﹨" G:max => _root_.Quotient (QuotientGroup.rightRel (α := G) H)

def DoubleCoset.ofLeft : G ⧸ K → H＼G／K :=
  Quotient.map id (by
    simp only [QuotientGroup.leftRel_apply, id_eq, Setoid.ker_def]
    intro a b hab
    exact .symm <| doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨1, by simp, _, hab, by simp⟩))

@[simp]
lemma DoubleCoset.ofLeft_mk (x : G) : ofLeft H K (QuotientGroup.mk x) = DoubleCoset.mk H K x := rfl

lemma DoubleCoset.ofLeft_surjective : Function.Surjective (ofLeft H K) :=
  Quotient.map_surjective _ Function.surjective_id

def DoubleCoset.ofRight : H﹨G → H＼G／K :=
  Quotient.map id (by
    simp only [QuotientGroup.rightRel_apply, id_eq, Setoid.ker_def]
    intro a b hab
    exact .symm <| doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨_, hab, 1, by simp, by simp⟩))

@[simp]
lemma DoubleCoset.ofRight_mk'' (x : G) : ofRight H K (.mk'' x) = DoubleCoset.mk H K x := rfl

lemma DoubleCoset.ofRight_surjective : Function.Surjective (ofRight H K) :=
  Quotient.map_surjective _ Function.surjective_id

open scoped Pointwise in
noncomputable
def DoubleCoset.toMapIdPreimage {G : Type*} [Group G] (H K₁ K₂ : Subgroup G) (eK : K₁ ≤ K₂)
  (g : G) : K₂ ⧸ K₁.subgroupOf K₂ →
      DoubleCoset.map H K₁ H K₂ (.id _) le_rfl eK ⁻¹' {DoubleCoset.mk _ _ g} := by
  refine Quotient.lift (fun k ↦ ⟨DoubleCoset.mk _ _ (g * ↑k), ?_⟩) ?_
  · suffices mk H K₂ (g * ↑k) = mk H K₂ g by simp [this]
    exact ((DoubleCoset.eq ..).mpr ⟨1, one_mem _, k.1, by simp⟩).symm
  · exact fun a b h ↦ Subtype.ext <| (DoubleCoset.eq ..).mpr
      ⟨1, one_mem _, _, (QuotientGroup.leftRel_apply.mp h:), by simp⟩

open scoped Pointwise in
lemma DoubleCoset.toMapIdPreimage_surjective
    {G : Type*} [Group G] (H K₁ K₂ : Subgroup G) (eK : K₁ ≤ K₂) (g : G) :
    Function.Surjective (toMapIdPreimage H K₁ K₂ eK g) := by
  refine Quotient.lift_surjective _ _ ?_
  suffices ∀ x, mk H K₂ x = mk H K₂ g → ∃ a ∈ K₂, mk H K₁ (g * a) = mk H K₁ x by
    simpa [Function.Surjective, (DoubleCoset.mk_surjective _ _).forall]
  simp only [eq]
  rintro x ⟨h, hh, k, hk, rfl⟩
  exact ⟨_, inv_mem hk, _, inv_mem hh, 1, by simp⟩

open scoped Pointwise in
open QuotientGroup in
/-- There is a bijection between `U / (gVg⁻¹ ∩ U)` and the image of `UgV` in `G / V`. -/
noncomputable
def _root_.QuotientGroup.quotientConjActEquivImageMulSingleton
    {G : Type*} [Group G]
    {g : G} {U V : Subgroup G} :
    U ⧸ (ConjAct.toConjAct g • V).subgroupOf U ≃
      (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)) := by
  refine .ofBijective (Quotient.lift (fun x ↦ ⟨_, _, Set.mul_mem_mul x.2 rfl, rfl⟩) ?_) ?_
  · intro a b e
    simpa [QuotientGroup.eq, QuotientGroup.leftRel_apply,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, -smul_mul',
      ConjAct.toConjAct_inv_smul', mul_assoc] using e
  · refine ⟨Quotient.ind₂ ?_, Quotient.lift_surjective _ _ ?_⟩
    · simp [Function.Surjective, -Set.image_mul_right]
    · simp [QuotientGroup.eq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, -smul_mul',
        ConjAct.toConjAct_inv_smul', mul_assoc]

open scoped Pointwise in
/--
Given `K₁ ≤ K₂`, the map `f : H\G/K₁ → H\G/K₂` is surjective.
For `HgK₂ : H\G/K₂`, there is a surjection `g : K₂/K₁ → f⁻¹(HgK₂), k ↦ H(gk)K₁`.
And for `H(gk)K₁ : f⁻¹(HgK₂)`, there set `g⁻¹(H(gk)K₁) = { aK₁ ∈ K₂/K₁ | a ∈ (gHg⁻¹ ∩ K₂)xK₁ }`
-/
lemma DoubleCoset.toMapIdPreimage_preimage
    {G : Type*} [Group G] (H K₁ K₂ : Subgroup G) (eK : K₁ ≤ K₂) (g : G) (x) :
    (toMapIdPreimage H K₁ K₂ eK g ⁻¹' {toMapIdPreimage H K₁ K₂ eK g x}) =
      DoubleCoset.ofLeft ((ConjAct.toConjAct g⁻¹ • H).subgroupOf K₂) _ ⁻¹'
        {DoubleCoset.ofLeft ((ConjAct.toConjAct g⁻¹ • H).subgroupOf K₂) _ x} := by
  ext a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  trans mk H K₁ (g * ↑a) = mk H K₁ (g * x)
  · simp [Subtype.ext_iff, toMapIdPreimage]
  simp only [eq, ofLeft_mk, Set.mem_preimage, Set.mem_singleton_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_smul_pointwise_iff_exists, ConjAct.toConjAct_smul, Subtype.ext_iff,
    Subgroup.coe_mul, Subtype.exists, exists_and_left, exists_prop, exists_exists_and_eq_and,
    inv_inv]
  refine ⟨fun ⟨b, hb, c, hc, e⟩ ↦ ⟨b, hb, ?_, c, hc, eK hc, ?_⟩,
    fun ⟨b, hb, hb', c, hc, hc', e⟩ ↦ ⟨_, hb, _, hc, ?_⟩⟩
  · convert_to x * c⁻¹ * a⁻¹ ∈ K₂
    · rw [mul_assoc, inv_mul_eq_iff_eq_mul]; simp [← mul_assoc, e]
    · exact mul_mem (mul_mem x.2 (inv_mem (eK hc))) (inv_mem a.2)
  · simp [mul_assoc, eq_inv_mul_iff_mul_eq, e]
  · simp [e, mul_assoc]

open scoped Pointwise in
theorem Subgroup.conjAct_smul_subgroupOf {G : Type*} [Group G] {P H : Subgroup G} (h : H) :
    ConjAct.toConjAct h • P.subgroupOf H = ((ConjAct.toConjAct h.1) • P).subgroupOf H := by
  ext; simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv_smul']

open scoped Pointwise in
/--
Given `K₁ ≤ K₂`, the map `f : H\G/K₁ → H\G/K₂` is surjective.
For `HgK₂ : H\G/K₂`, there is a surjection `g : K₂/K₁ → f⁻¹(HgK₂), x ↦ H(gx)K₁`.
This sends `[K₂ ⊓ gx⁻¹Hgx : K₁ ⊓ (gx)⁻¹Hgx]` elements to `H(gx)K₁`.
-/
lemma DoubleCoset.ncard_toMapIdPreimage_preimage
    {G : Type*} [Group G] (H K₁ K₂ : Subgroup G) (eK : K₁ ≤ K₂) (g : G) (x : K₂) :
    Set.ncard (toMapIdPreimage H K₁ K₂ eK g ⁻¹'
      {toMapIdPreimage H K₁ K₂ eK g (QuotientGroup.mk x)}) =
      (K₁).relIndex (K₂ ⊓ ConjAct.toConjAct (g * x)⁻¹ • H) := by
  rw [DoubleCoset.toMapIdPreimage_preimage]
  convert (Nat.card_congr (QuotientGroup.quotientConjActEquivImageMulSingleton (g := x)
    (U := (ConjAct.toConjAct g⁻¹ • H).subgroupOf K₂) (V := K₁.subgroupOf K₂))).symm
  · simp only [Nat.card_coe_set_eq]
    congr 1
    ext a
    obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective a
    suffices (∃ b, g * b * g⁻¹ ∈ H ∧ a⁻¹ * b⁻¹ * x ∈ K₁ ∧ b ∈ K₂ ∧ a⁻¹ * b⁻¹ * x ∈ K₂) ↔
        ∃ b, g * (b * x⁻¹) * g⁻¹ ∈ H ∧ b ∈ K₂ ∧ b⁻¹ * a ∈ K₁ by
      simpa [-ConjAct.toConjAct_inv, DoubleCoset.eq, Subtype.ext_iff,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem, QuotientGroup.eq,
        ConjAct.smul_def, mul_assoc, ← inv_mul_eq_iff_eq_mul] using this
    trans ∃ b, g * b * g⁻¹ ∈ H ∧ a⁻¹ * b⁻¹ * x ∈ K₁ ∧ b ∈ K₂
    · have := SetLike.le_def.mp eK; grind
    conv_rhs => rw [(mul_right_surjective (x : G)).exists, inv_surjective.exists]
    simp [Subgroup.mul_mem_cancel_right]
    simp [← inv_mem_iff (x := _ * _⁻¹ * _), ← mul_assoc, and_comm]
  · rw [← Subgroup.index, ← Subgroup.relIndex, Subgroup.conjAct_smul_subgroupOf,
      Subgroup.subgroupOf, Subgroup.relIndex_comap,
      ← Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct x.1)]
    congr 1
    have : ConjAct.toConjAct x.1 • K₂ = K₂ :=
      Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer x.2)
    simp [← mul_smul, this, inf_comm]

open scoped Pointwise in
lemma DoubleCoset.sum_filter_map_eq_relIndex_eq_relIndex
    {G : Type*} [Group G] (H K₁ K₂ : Subgroup G) (eK : K₁ ≤ K₂)
    (g : H＼G／K₂) [Fintype (H＼G／K₁)] [DecidableEq (H＼G／K₂)] [K₁.IsFiniteRelIndex K₂] :
      ∑ a : H＼G／K₁ with DoubleCoset.map H K₁ H K₂ (.id _) le_rfl eK a = g,
      a.lift (fun i ↦ K₁.relIndex (K₂ ⊓ ConjAct.toConjAct i⁻¹ • H)) (by
      intro a b e
      obtain ⟨b, hb, c, hc, rfl⟩ := DoubleCoset.rel_iff.mp e
      have H₁ : ConjAct.toConjAct c • K₁ = K₁ :=
        Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hc)
      have H₂ : ConjAct.toConjAct c • K₂ = K₂ :=
        Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer (eK hc))
      have H₃ : (ConjAct.toConjAct b)⁻¹ • H = H :=
        Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer (inv_mem hb))
      trans K₁.relIndex (K₂ ⊓ (ConjAct.toConjAct c)⁻¹ • (ConjAct.toConjAct a)⁻¹ • H)
      · rw [eq_comm, ← Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct c)]
        simp [H₁, H₂]
      · simp [mul_smul, H₃]) =
      K₁.relIndex K₂ := by
  classical
  obtain ⟨g, rfl⟩ := DoubleCoset.mk_surjective _ _ g
  trans ∑ a, Set.ncard (toMapIdPreimage H K₁ K₂ eK g ⁻¹' {a})
  · rw [← Finset.sum_attach]
    refine (Equiv.sum_comp (Equiv.subtypeEquivRight Finset.mem_filter_univ).symm _).symm.trans ?_
    refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun a _ ↦ ?_
    obtain ⟨a, rfl⟩ := toMapIdPreimage_surjective _ _ _ _ _ a
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    rw [DoubleCoset.ncard_toMapIdPreimage_preimage]
    simp only [toMapIdPreimage, Quotient.lift_mk, Equiv.subtypeEquivRight_symm_apply_coe]
  rw [← finsum_eq_sum_of_fintype, ← Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _)]
  · rw [← Set.preimage_iUnion, Set.iUnion_of_singleton, Set.preimage_univ]
    simp
    rfl
  · generalize toMapIdPreimage H K₁ K₂ eK g = F
    simp [Pairwise, Function.onFun, Set.disjoint_iff]; grind

lemma DoubleCoset.σ_exists :
    ∃ (σ : H＼G／K → G) (x : G → H) (y : G → K),
    (∀ a, a = x a * σ (DoubleCoset.mk H K a) * y a) ∧
    (∀ a, x (σ a) = 1) ∧ (∀ a, y (σ a) = 1) ∧ (σ (mk H K 1) = 1) ∧
    (∀ a, ∀ k : K, x (a * k) = x a) := by
  have (x : H＼G／K) : ∃ (a : G ⧸ K),
      DoubleCoset.ofLeft H K a = x ∧ (x = DoubleCoset.mk H K 1 → a = ↑(1 : G)) := by
    obtain rfl | h := eq_or_ne x (DoubleCoset.mk H K 1)
    · simp
    · obtain ⟨x, rfl⟩ := DoubleCoset.ofLeft_surjective H K x
      exact ⟨x, by simp [h]⟩
  choose σ hσ hσ₁ using this
  have (x : G ⧸ K) : ∃ (a : G), ↑a = x ∧ (x = ↑(1 : G) → a = 1) := by
    obtain rfl | h := eq_or_ne x ↑(1 : G)
    · simp
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨x, by simp [h]⟩
  choose τ hτ hτ₁ using this
  simp only [forall_eq] at hσ₁ hτ₁
  have hτ' (a : G ⧸ K) : mk H K (τ a) = ofLeft H K a := congr(ofLeft H K $(hτ a))
  have (a : G ⧸ K) : ∃ x : H, a = x.1 • σ (ofLeft H K a) ∧ ((∃ b, a = σ b) → x = 1) := by
    by_cases ha : ∃ b, a = σ b
    · suffices a = σ (ofLeft H K a) by simpa [ha]
      grind
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, e⟩ := QuotientGroup.mk_surjective (σ (mk H K a))
    suffices ∃ c ∈ H, (a : G ⧸ K) = ↑(c * b) by simpa [ha, ← e]
    obtain ⟨x, y, rfl⟩ : ∃ h : H, ∃ k : K, a = h * b * k := by
      simpa [← e, DoubleCoset.eq] using hσ (mk H K a)
    simp; grind
  choose x hx hxσ using this
  simp only [forall_exists_index, forall_eq_apply_imp_iff] at hxσ
  have (a : G) : ∃ k : K, a = x a * τ (σ (mk H K a)) * k ∧ ((∃ b, a = τ (σ b)) → k = 1) := by
    by_cases ha : ∃ b, a = τ (σ b)
    · suffices a = ↑(x ↑a) * τ (σ (mk H K a)) by simpa [ha]
      obtain ⟨b, rfl⟩ := ha
      simp [hτ', hσ, hxσ, hτ]
    · suffices ∃ k : K, a = x a * τ (σ (mk H K a)) * k by simpa [ha]
      refine ⟨⟨(a⁻¹ * (↑(x ↑a) * τ (σ (mk H K a))))⁻¹, inv_mem ?_⟩, by simp [mul_assoc]⟩
      simpa [QuotientGroup.eq] using (hx a).trans congr(_ • $(hτ (σ _))).symm
  choose y hy hyτ using this
  simp only [forall_exists_index, forall_eq_apply_imp_iff] at hyτ
  exact ⟨τ ∘ σ, x ∘ (↑), y, by grind, by grind, by grind, by grind, by simp⟩

variable {H K} in
noncomputable def DoubleCoset.σ (g : H＼G／K) : G := (DoubleCoset.σ_exists H K).choose g
noncomputable def DoubleCoset.σLeft (g : G) : H := (DoubleCoset.σ_exists H K).choose_spec.choose g
noncomputable def DoubleCoset.σRight (g : G) : K :=
  (DoubleCoset.σ_exists H K).choose_spec.choose_spec.choose g

lemma DoubleCoset.σ_spec (g : G) :
    σLeft H K g * σ (mk H K g) * σRight H K g = g :=
  ((DoubleCoset.σ_exists H K).choose_spec.choose_spec.choose_spec.1 g).symm

@[simp] lemma DoubleCoset.σLeft_σ (g : H＼G／K) : σLeft H K (σ g) = 1 :=
  (DoubleCoset.σ_exists H K).choose_spec.choose_spec.choose_spec.2.1 g

@[simp] lemma DoubleCoset.σRight_σ (g : H＼G／K) : σRight H K (σ g) = 1 :=
  (DoubleCoset.σ_exists H K).choose_spec.choose_spec.choose_spec.2.2.1 g

@[simp] lemma DoubleCoset.σ_one : σ (mk H K 1) = 1 :=
  (DoubleCoset.σ_exists H K).choose_spec.choose_spec.choose_spec.2.2.2.1

@[simp] lemma DoubleCoset.σLeft_mul (g : G) (k : K) : σLeft H K (g * k) = σLeft H K g :=
  (DoubleCoset.σ_exists H K).choose_spec.choose_spec.choose_spec.2.2.2.2 g k

@[simp] lemma DoubleCoset.σRight_mul (g : G) (k : K) : σRight H K (g * k) = σRight H K g * k := by
  apply Subtype.ext <| mul_right_injective (σLeft H K g * σ (mk H K g)) ?_
  simp only [Subgroup.coe_mul, ← mul_assoc, DoubleCoset.σ_spec]
  convert DoubleCoset.σ_spec H K (g * k) using 4
  · simp
  · exact (DoubleCoset.eq _ _ _ _).mpr ⟨1, by simp, k, k.2, by simp⟩

@[simp] lemma DoubleCoset.σLeft_one : σLeft H K 1 = 1 := by rw [← σ_one, σLeft_σ]
@[simp] lemma DoubleCoset.σRight_one : σRight H K 1 = 1 := by rw [← σ_one, σRight_σ]

@[simp] lemma DoubleCoset.σ_of_mem_left (g : G) (hg : g ∈ H) : σ (mk H K g) = 1 := by
  convert σ_one H K using 2; exact ((DoubleCoset.eq ..).mpr ⟨g, hg, 1, by simp⟩).symm

@[simp] lemma DoubleCoset.σ_of_mem_right (g : G) (hg : g ∈ K) : σ (mk H K g) = 1 := by
  convert σ_one H K using 2; exact ((DoubleCoset.eq ..).mpr ⟨1, by simp, g, by simp [hg]⟩).symm

@[simp] lemma DoubleCoset.σRight_eq_self (g : K) : σRight H K g = g := by
  simpa using σRight_mul H K 1 g

@[simp] lemma DoubleCoset.σLeft_of_mem (g : G) (hg : g ∈ K) : σLeft H K g = 1 := by
  lift g to K using hg
  simpa using DoubleCoset.σ_spec H K g
