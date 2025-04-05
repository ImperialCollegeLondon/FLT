import FLT.Patching.Utils.AdicTopology
import FLT.Patching.Ultraproduct

variable (Λ : Type*) {ι : Type*} [CommRing Λ] (R : ι → Type*)
variable [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, Algebra Λ (R i)]
variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
variable [∀ i, CompactSpace (R i)] [∀ i, IsLocalRing.IsAdicTopology (R i)]
variable (F : Ultrafilter ι)
variable [TopologicalSpace Λ] [IsTopologicalRing Λ] [∀ i, ContinuousSMul Λ (R i)]
variable [Algebra.TopologicallyFG ℤ Λ]

open IsLocalRing

-- This is true when `R i` is topologically fg over `𝒪` by a bounded number of generators, and
-- for each `k`, the index of `m_Λ ⊔ mᵢᵏ` in `Rᵢ` is uniformly bounded.
-- The latter is true when all `Rᵢ/m_Λ` are isomorphic.
class Algebra.UniformlyBoundedRank : Prop where
  cond : ∀ k, ∃ n : ℕ, ∀ i, Nat.card (R i ⧸ maximalIdeal (R i) ^ k) < n

variable [Algebra.UniformlyBoundedRank R]

abbrev PatchingAlgebra.Component (k : ℕ) := UltraProduct (fun i ↦ R i ⧸ maximalIdeal (R i) ^ k) F

instance (k) : T2Space (PatchingAlgebra.Component R F k) := DiscreteTopology.toT2Space

lemma PatchingAlgebra.componentEquiv (k) : ∀ᶠ j in F,
    Nonempty (PatchingAlgebra.Component R F k ≃ₐ[Λ] R j ⧸ maximalIdeal (R j) ^ k) := by
  obtain ⟨n, hn⟩ := Algebra.UniformlyBoundedRank.cond (R := R) k
  refine UltraProduct.exists_algEquiv_of_bddAbove_card F n (.of_forall ?_) (.of_forall ?_)
  · exact fun x ↦ ⟨AddSubgroup.quotient_finite_of_isOpen _ (isOpen_maximalIdeal_pow _ _), hn _⟩
  · exact fun i ↦ ((maximalIdeal (R i) ^ k).restrictScalars Λ).continuousSMul_quotient

instance (k : ℕ) : Finite (PatchingAlgebra.Component R F k) :=
  (PatchingAlgebra.componentEquiv ℤ R F k).exists.choose_spec.some.finite_iff.mpr
    (AddSubgroup.quotient_finite_of_isOpen _ (isOpen_maximalIdeal_pow _ _))

instance (k : ℕ) [NeZero k] : Nontrivial (PatchingAlgebra.Component R F k) := by
  obtain ⟨i, ⟨e⟩⟩ := (PatchingAlgebra.componentEquiv ℤ R F k).exists
  have : Nontrivial (R i ⧸ maximalIdeal (R i) ^ k) := by
    refine Ideal.Quotient.nontrivial ?_
    exact ((Ideal.pow_le_self (NeZero.ne k)).trans_lt
      (lt_top_iff_ne_top.mpr (maximalIdeal.isMaximal (R i)).ne_top)).ne
  exact e.toRingHom.domain_nontrivial

instance : Subsingleton (PatchingAlgebra.Component R F 0) := by
  obtain ⟨i, ⟨e⟩⟩ := (PatchingAlgebra.componentEquiv ℤ R F 0).exists
  have : Subsingleton (R i ⧸ maximalIdeal (R i) ^ 0) := by
    simp [Submodule.subsingleton_quotient_iff_eq_top]
  exact e.symm.toRingHom.codomain_trivial

instance (k : ℕ) [NeZero k] : IsLocalRing (PatchingAlgebra.Component R F k) :=
  let ⟨i, ⟨e⟩⟩ := (PatchingAlgebra.componentEquiv ℤ R F k).exists
  .of_surjective' (e.symm.toRingHom.comp (Ideal.Quotient.mk (maximalIdeal (R i) ^ k))) <|
    e.symm.surjective.comp Ideal.Quotient.mk_surjective

instance : Nontrivial (Π k, PatchingAlgebra.Component R F k) :=
  (Pi.evalRingHom _ 1).domain_nontrivial

abbrev PatchingAlgebra.componentMap (j k : ℕ) (hjk : k ≤ j) : Component R F j →+* Component R F k :=
  UltraProduct.mapRingHom (R := fun i ↦ R i ⧸ maximalIdeal (R i) ^ j) F fun _ ↦
    Ideal.quotientMap _ (.id _) (Ideal.pow_le_pow_right hjk)

instance (j k : ℕ) (hjk : k ≤ j) [NeZero k] : IsLocalHom (PatchingAlgebra.componentMap R F j k hjk) := by
  suffices ∀ (i : ι), IsLocalHom (Ideal.quotientMap (maximalIdeal (R i) ^ k)
      (.id (R i)) (Ideal.pow_le_pow_right hjk)) by
    delta PatchingAlgebra.componentMap; infer_instance
  intro i
  have : Nontrivial (R i ⧸ maximalIdeal (R i) ^ k) := Ideal.Quotient.nontrivial
    ((Ideal.pow_le_self (NeZero.ne k)).trans_lt
      (lt_top_iff_ne_top.mpr (maximalIdeal.isMaximal (R i)).ne_top)).ne
  have : Nontrivial (R i ⧸ maximalIdeal (R i) ^ j) := Ideal.Quotient.nontrivial
    ((Ideal.pow_le_self ((Nat.pos_of_neZero k).trans_le hjk).ne').trans_lt
      (lt_top_iff_ne_top.mpr (maximalIdeal.isMaximal (R i)).ne_top)).ne
  have : IsLocalRing (R i ⧸ maximalIdeal (R i) ^ j) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  exact .of_surjective _ (Ideal.quotientMap_surjective RingHomSurjective.is_surjective)

def PatchingAlgebra.subring : Subring (Π i, Component R F i) where
  carrier := { v | ∀ j k hjk, componentMap R F j k hjk (v j) = v k }
  mul_mem' := by simp +contextual only [Set.mem_setOf, Pi.mul_apply, map_mul, implies_true]
  add_mem' := by simp +contextual only [Set.mem_setOf, Pi.add_apply, RingHom.map_add, implies_true]
  one_mem' := by simp
  zero_mem' := by simp
  neg_mem' := by simp +contextual only [Set.mem_setOf, Pi.neg_apply, RingHom.map_neg, implies_true]

def PatchingAlgebra.subalgebra : Subalgebra Λ (Π i, Component R F i) where
  __ := subring R F
  algebraMap_mem' _ _ _ _ := rfl

omit [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
  [∀ i, CompactSpace (R i)] [∀ i, IsLocalRing.IsAdicTopology (R i)]
  [Algebra.UniformlyBoundedRank R] in
lemma PatchingAlgebra.isClosed_subring :
    IsClosed (X := Π i, Component R F i) (subring R F) := by
  have (j k h) : IsClosed { v : Π i, Component R F i | componentMap R F j k h (v j) = v k } := by
    exact isClosed_eq (by continuity) (by continuity)
  convert isClosed_iInter fun j ↦ isClosed_iInter fun k ↦ isClosed_iInter (this j k)
  ext; simp; rfl

def PatchingAlgebra : Type _ := PatchingAlgebra.subring R F

instance : CommRing (PatchingAlgebra R F) :=
  inferInstanceAs (CommRing (PatchingAlgebra.subring R F))

instance : Algebra Λ (PatchingAlgebra R F) :=
  inferInstanceAs (Algebra Λ (PatchingAlgebra.subalgebra Λ R F))

instance : TopologicalSpace (PatchingAlgebra R F) :=
  inferInstanceAs (TopologicalSpace (PatchingAlgebra.subring R F))

instance : IsTopologicalRing (PatchingAlgebra R F) :=
  inferInstanceAs (IsTopologicalRing (PatchingAlgebra.subring R F))

instance : T2Space (PatchingAlgebra R F) :=
  (Topology.IsEmbedding.subtypeVal).t2Space

instance : CompactSpace (PatchingAlgebra R F) :=
  (IsClosed.isClosedEmbedding_subtypeVal (PatchingAlgebra.isClosed_subring R F)).compactSpace

instance : Nontrivial (PatchingAlgebra R F) := (PatchingAlgebra.subring R F).subtype.domain_nontrivial

instance : IsLocalHom (PatchingAlgebra.subring R F).subtype := by
  constructor
  intro a H
  rw [IsUnit.pi_iff] at H
  refine (isUnit_iff_exists_inv.mpr ⟨⟨fun i ↦ ↑((H i).unit⁻¹), fun i j hij ↦ ?_⟩,
    Subtype.ext (funext fun i ↦ (H i).mul_val_inv)⟩)
  dsimp only
  rw [← MonoidHom.coe_coe, ← RingHom.toMonoidHom_eq_coe, ← Units.coe_map_inv]
  congr
  ext
  simpa using a.2 i j hij

instance : IsLocalRing (PatchingAlgebra R F) := by
  constructor
  intro a b e
  wlog H : ∀ i, IsUnit (a.1 i) generalizing a b
  · obtain ⟨i, hi⟩ := not_forall.mp H
    have hb : ∀ j > i, IsUnit (b.1 j) := by
      intro j hj
      have : NeZero j := NeZero.of_gt hj
      exact (isUnit_or_isUnit_of_add_one (congr_fun (congr_arg Subtype.val e) j)).resolve_left
        fun H ↦ hi (a.2 _ _ hj.le ▸ H.map (PatchingAlgebra.componentMap R F j i hj.le))
    replace hb : ∀ j, IsUnit (b.1 j) := by
      intro j
      by_cases hij : i < j
      · exact hb j hij
      rw [← b.2 _ _ ((le_of_not_lt hij).trans i.le_succ)]
      exact (hb _ i.lt_succ_self).map _
    exact (this ((add_comm b a).trans e) hb).symm
  exact .inl (IsUnit.of_map (PatchingAlgebra.subring R F).subtype _ (IsUnit.pi_iff.mpr H))

instance (i) [NeZero i] : IsLocalHom ((Pi.evalRingHom _ i).comp (PatchingAlgebra.subring R F).subtype) := by
  constructor
  intro a H
  apply isUnit_of_map_unit (PatchingAlgebra.subring R F).subtype
  rw [IsUnit.pi_iff]
  intro j
  obtain hij | hij := le_total i j
  · apply isUnit_of_map_unit (PatchingAlgebra.componentMap R F _ _ hij)
    dsimp
    rwa [a.2 _ _ hij]
  · dsimp
    rw [← a.2 _ _ hij]
    exact H.map (PatchingAlgebra.componentMap R F _ _ hij)

instance : TotallyDisconnectedSpace (PatchingAlgebra R F) :=
  Subtype.totallyDisconnectedSpace

variable {Rₒₒ} [CommRing Rₒₒ] (f : ∀ i, Rₒₒ →+* R i) [TopologicalSpace Rₒₒ]
variable [IsTopologicalRing Rₒₒ] [Algebra.TopologicallyFG ℤ Rₒₒ]
variable (hf : ∀ i, Continuous (f i))

def PatchingAlgebra.lift : Rₒₒ →+* PatchingAlgebra R F :=
  (Pi.ringHom fun i ↦ (UltraProduct.π _ _).comp
    (Pi.ringHom fun j ↦ (Ideal.Quotient.mk _).comp (f j))).codRestrict _ <| by
  intro x i j hij
  simp [componentMap, UltraProduct.mapRingHom_π]

include hf in
lemma PatchingAlgebra.continuous_lift : Continuous (lift R F f) := by
  refine continuous_induced_rng.mpr ?_
  refine continuous_pi fun k ↦ ?_
  obtain ⟨n, hn⟩ := Algebra.UniformlyBoundedRank.cond (R := R) k
  refine UltraProduct.continuous_of_bddAbove_card F n (.of_forall ?_) _ (.of_forall ?_)
  · exact fun x ↦ ⟨AddSubgroup.quotient_finite_of_isOpen _ (isOpen_maximalIdeal_pow _ _), hn _⟩
  · exact fun i ↦ (continuous_algebraMap _ _).comp (hf i)

variable [CompactSpace Rₒₒ]

include hf in
lemma PatchingAlgebra.lift_surjective (hf' : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (lift R F f) := by
  suffices DenseRange (lift R F f) by
    rw [← Set.range_eq_univ, ← this.closure_eq,
      (isCompact_range (continuous_lift R F f hf)).isClosed.closure_eq]
  refine denseRange_inverseLimit (ι := ℕᵒᵈ) _ _ (fun _ _ _ ↦ continuous_of_discreteTopology) _ ?_
  refine fun i ↦ denseRange_discrete.mpr ?_
  obtain ⟨n, hn⟩ := Algebra.UniformlyBoundedRank.cond (R := R) i
  refine UltraProduct.surjective_of_bddAbove_card F n (.of_forall ?_) _ (.of_forall ?_) (.of_forall ?_)
  · exact fun x ↦ ⟨AddSubgroup.quotient_finite_of_isOpen _ (isOpen_maximalIdeal_pow _ _), hn _⟩
  · exact fun x ↦ (continuous_algebraMap _ _).comp (hf x)
  · exact fun x ↦ Ideal.Quotient.mk_surjective.comp (hf' x)

def PatchingAlgebra.ofPi :
    (ℕ → Π i, R i) →+* Π k, Component R F k :=
  Pi.ringHom fun k ↦ (RingHom.comp ((Ideal.Quotient.mk
    (eventuallyProd (R := fun i ↦ R i ⧸ maximalIdeal (R i) ^ k)
    (M := fun i ↦ R i ⧸ maximalIdeal (R i) ^ k) ⊥ F)).comp
    (Pi.ringHom fun j ↦ (Ideal.Quotient.mk _).comp (Pi.evalRingHom _ j))) (Pi.evalRingHom _ k))

variable {R F} in
omit
  [∀ (i : ι), TopologicalSpace (R i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [Algebra.UniformlyBoundedRank R] in
lemma PatchingAlgebra.ofPi_surjective :
    Function.Surjective (ofPi R F) := by
  intro x
  have (k : ℕ) := Ideal.Quotient.mk_surjective
    (I := (eventuallyProd (R := fun i ↦ R i ⧸ maximalIdeal (R i) ^ k)
      (M := fun i ↦ R i ⧸ maximalIdeal (R i) ^ k) ⊥ F)) (x k)
  choose y hy using this
  choose z hz using fun k i ↦ Ideal.Quotient.mk_surjective (y k i)
  refine ⟨z, funext fun k ↦ ?_⟩
  rw [← hy]
  show Ideal.Quotient.mk _ _ = _
  congr 1
  ext i
  simp only [Pi.evalRingHom_apply, Pi.ringHom_apply, RingHom.coe_comp, Function.comp_apply, hz]

omit
  [∀ (i : ι), TopologicalSpace (R i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [Algebra.UniformlyBoundedRank R] in
@[simp]
lemma PatchingAlgebra.ofPi_apply (x k) :
  ofPi R F x k = UltraProduct.π (fun i ↦ R i ⧸ maximalIdeal (R i) ^ k) F
    (fun i ↦ Ideal.Quotient.mk _ (x k i)) := rfl

def PatchingAlgebra.incl :
    (Π i, R i) →+* PatchingAlgebra R F :=
  RingHom.codRestrict ((ofPi R F).comp (Pi.ringHom fun _ ↦ .id _)) (subring R F) <| by
    intro x j k h
    simp [UltraProduct.mapRingHom_π]

section Functorial

variable {R' : ι → Type*} [∀ i, CommRing (R' i)] [∀ i, IsLocalRing (R' i)] --[∀ i, Module R' (N i)]
variable {R'' : ι → Type*} [∀ i, CommRing (R'' i)] [∀ i, IsLocalRing (R'' i)] --[∀ i, Module R (N' i)]
variable (f : ∀ i, R i →+* R' i) (g : ∀ i, R' i →+* R'' i)
variable [∀ i, IsLocalHom (f i)] [∀ i, IsLocalHom (g i)]

abbrev PatchingAlgebra.componentMapRingHom (k : ℕ) :
    Component R F k →+* Component R' F k :=
  UltraProduct.mapRingHom F
    (R := fun i ↦ R i ⧸ maximalIdeal (R i) ^ k)
    (S := fun i ↦ R' i ⧸ maximalIdeal (R' i) ^ k)
    fun i ↦ Ideal.quotientMap _ (f i) <| by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      apply Ideal.pow_right_mono
      exact ((local_hom_TFAE (f i)).out 0 2).mp (by infer_instance)

omit
  [∀ (i : ι), TopologicalSpace (R i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [Algebra.UniformlyBoundedRank R] in
lemma PatchingAlgebra.componentMapRingHom_surjective
    (hf : ∀ i, Function.Surjective (f i)) (k : ℕ) :
    Function.Surjective (componentMapRingHom R F f k) := by
  apply UltraProduct.mapRingHom_surjective
  intro i x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective.comp (hf i) x
  refine ⟨Ideal.Quotient.mk _ x, by simp⟩

variable {R} in
def PatchingAlgebra.map :
    PatchingAlgebra R F →+* PatchingAlgebra R' F :=
  RingHom.restrict (Pi.ringHom fun i ↦ (componentMapRingHom R F f i).comp (Pi.evalRingHom _ _))
    _ _ <| by
    intro x hx i j hij
    obtain ⟨a, ha⟩ := UltraProduct.π_surjective (x i)
    simp only [Pi.ringHom_apply, RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply, ←
      hx i j hij, ← ha, UltraProduct.mapRingHom_π, UltraProduct.π_eq_iff]
    filter_upwards with k
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (a k)
    simp only [← hb, Ideal.quotientMap_mk, RingHomCompTriple.comp_apply, RingHom.id_apply]

-- omit [IsTopologicalRing R] [CompactSpace R] in
omit
  [∀ (i : ι), TopologicalSpace (R i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [Algebra.UniformlyBoundedRank R] in
@[simp]
lemma PatchingAlgebra.map_apply (x : PatchingAlgebra R F) (k) :
    (map F f x).1 k = componentMapRingHom R F f k (x.1 k) := rfl

-- omit [IsTopologicalRing R] [CompactSpace R] in
omit
  [∀ (i : ι), TopologicalSpace (R i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [Algebra.UniformlyBoundedRank R] in
lemma PatchingAlgebra.map_comp_apply (x) :
    map F (fun i ↦ (g i).comp (f i)) x = map F g (map F f x) := by
  refine Subtype.ext (funext fun k ↦ ?_)
  obtain ⟨y, hy⟩ := ofPi_surjective x.1
  simp [← hy, UltraProduct.mapRingHom_π]

omit
  [∀ (i : ι), TopologicalSpace (R i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [Algebra.UniformlyBoundedRank R] in
lemma PatchingAlgebra.map_comp :
    map F (fun i ↦ (g i).comp (f i)) = (map F g).comp (map F f) :=
  RingHom.ext (map_comp_apply R F f g)

omit
  [∀ (i : ι), TopologicalSpace (R i)]
  [∀ (i : ι), IsTopologicalRing (R i)]
  [∀ (i : ι), CompactSpace (R i)]
  [∀ (i : ι), IsAdicTopology (R i)]
  [Algebra.UniformlyBoundedRank R] in
@[simp]
lemma PatchingAlgebra.map_id :
    map F (fun i ↦ RingHom.id (R i)) = RingHom.id _ := by
  ext x
  obtain ⟨y, hy⟩ := ofPi_surjective x.1
  refine Subtype.ext (funext fun α ↦ ?_)
  simp [← hy, UltraProduct.mapRingHom_π]

instance {R S} [Semiring R] [Semiring S] (e : R ≃+* S) : IsLocalHom e.toRingHom :=
  ⟨fun x hx ↦ by convert hx.map e.symm; simp⟩

@[simps! apply symm_apply]
def PatchingAlgebra.mapEquiv (f : ∀ i, R i ≃+* R' i) :
    PatchingAlgebra R F ≃+* PatchingAlgebra R' F where
  __ := map F fun i ↦ (f i).toRingHom
  invFun := map F fun i ↦ (f i).symm.toRingHom
  left_inv x := by simp [← map_comp_apply]
  right_inv x := by simp [← map_comp_apply]

lemma RingHom.continuous_of_finite_of_compact {R H : Type*} [CommRing R] [Semiring H]
    (f : R →+* H) [TopologicalSpace R] [TopologicalSpace H] [CompactSpace R] [_root_.Finite H]
    [IsTopologicalRing R] [T2Space R] [IsNoetherianRing R] [ContinuousAdd H] :
    Continuous f := by
  suffices IsOpen (X := R) (RingHom.ker f) by
    apply continuous_of_continuousAt_zero
    rw [ContinuousAt, map_zero]
    refine (Filter.tendsto_zero.mpr (this.mem_nhds (map_zero f))).trans ?_
    simp +contextual [le_nhds_iff]
  have : (RingHom.ker f).toAddSubgroup.FiniteIndex := by
    have : _root_.Finite (R ⧸ (RingHom.ker f).toAddSubgroup) :=
      _root_.Finite.of_injective _ f.kerLift_injective
    exact AddSubgroup.finiteIndex_of_finite_quotient _
  have := (isCompact_of_isNoetherianRing (RingHom.ker f)).isClosed
  exact AddSubgroup.isOpen_of_isClosed_of_finiteIndex (RingHom.ker f).toAddSubgroup this

open IsLocalRing in
lemma PatchingAlgebra.map_surjective
    (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (map F f) := by
  intro x
  let s (k : ℕ) : Set (Component R F k) :=
    componentMapRingHom R F f k ⁻¹' {x.1 k}
  let fs (k₁ k₂ : ℕᵒᵈ) (h : k₁ ≤ k₂) (a : s k₁) : s k₂ :=
    ⟨componentMap R F _ _ h a.1, by
      have : _ = _ := a.2
      simp only [Set.mem_preimage, Set.mem_singleton_iff, s, ← x.2 _ _ h, ← this]
      obtain ⟨b, hb⟩ := UltraProduct.π_surjective a.1
      simp only [Pi.ringHom_apply, RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
        ← hb, UltraProduct.mapRingHom_π, UltraProduct.π_eq_iff]
      filter_upwards with k
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (b k)
      simp only [← hc, Ideal.quotientMap_mk, RingHomCompTriple.comp_apply, RingHom.id_apply]⟩
  have (k) : Nonempty (s k) := by
    simp only [nonempty_subtype, Set.mem_preimage, Set.mem_singleton_iff, s]
    exact PatchingAlgebra.componentMapRingHom_surjective R F f hf k (x.1 k)
  obtain ⟨v, hv⟩ := nonempty_inverseLimit_of_finite (ι := ℕᵒᵈ) (s ·) fs (by
      intro i
      ext ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := UltraProduct.π_surjective x
      simp only [Pi.ringHom_apply, RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
         UltraProduct.mapRingHom_π, UltraProduct.π_eq_iff, id_eq, fs]
      filter_upwards with k
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x k)
      simp only [← hb, Ideal.quotientMap_mk, RingHom.id_apply]) (by
      intro i j k hij hjk
      ext ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := UltraProduct.π_surjective x
      simp only [Pi.ringHom_apply, RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
         UltraProduct.mapRingHom_π, UltraProduct.π_eq_iff, id_eq, fs]
      filter_upwards with k
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x k)
      simp only [← hb, Ideal.quotientMap_mk, RingHom.id_apply])
      (l := id) (fun _ _ ↦ id) (fun a ↦ ⟨a, le_rfl⟩)
  refine ⟨⟨fun i ↦ (v i).1, fun α β h ↦ congr_arg Subtype.val (hv α β h)⟩, ?_⟩
  refine Subtype.ext (funext fun α ↦ ?_)
  have : _ = _ := (v α).2
  simpa using this

end Functorial

lemma PatchingAlgebra.algebraMap_continuous
    (R : Type*) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [IsNoetherianRing R] [IsAdicTopology R] :
    Continuous (algebraMap R (PatchingAlgebra (fun _ ↦ R) F)) := by
  refine continuous_induced_rng.mpr ?_
  refine continuous_pi fun k ↦ ?_
  let f : R →+* Component (fun x ↦ R) F k := (UltraProduct.π _ _).comp
    (Pi.ringHom fun i ↦ Ideal.Quotient.mk _)
  have : Algebra.UniformlyBoundedRank fun _ : ι ↦ R :=
    ⟨fun k ↦ ⟨(Nat.card (R ⧸ maximalIdeal R ^ k)).succ, fun _ ↦ Nat.lt_succ_self _⟩⟩
  have : Finite (Component (fun x ↦ R) F k) := instFiniteComponent _ _ k
  exact RingHom.continuous_of_finite_of_compact f

lemma PatchingAlgebra.algebraMap_surjective
    (R : Type*) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [IsNoetherianRing R] [IsAdicTopology R] :
    Function.Surjective (algebraMap R (PatchingAlgebra (fun _ ↦ R) F)) := by
  suffices DenseRange (algebraMap R (PatchingAlgebra (fun _ ↦ R) F)) by
    rw [← Set.range_eq_univ, ← this.closure_eq,
      (isCompact_range (algebraMap_continuous F R)).isClosed.closure_eq]
  refine denseRange_inverseLimit (ι := ℕᵒᵈ) _ _
    (fun _ _ _ ↦ continuous_of_discreteTopology) _
    fun k ↦ denseRange_discrete.mpr ?_
  have : Finite (R ⧸ maximalIdeal R ^ k) := AddSubgroup.quotient_finite_of_isOpen _
    (isOpen_maximalIdeal_pow _ _)
  have := UltraProduct.surjective_of_eventually_surjective
    (f := fun i : ι ↦ LinearMap.id (R := R) (M := R ⧸ maximalIdeal R ^ k)) F
    (.of_forall fun _ _ ↦ ⟨_, rfl⟩)
  exact this.comp Ideal.Quotient.mk_surjective

noncomputable
def PatchingAlgebra.constEquiv
    (R : Type*) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [IsNoetherianRing R] [IsAdicTopology R] :
    R ≃ₐ[R] PatchingAlgebra (fun _ ↦ R) F := by
  refine .ofBijective (Algebra.ofId R (PatchingAlgebra (fun _ ↦ R) F))
    ⟨?_, algebraMap_surjective F R⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have (k : ℕ) : a ∈ maximalIdeal R ^ k  := by
    have := UltraProduct.πₗ_eq_zero.mp (congr_fun (congr_arg Subtype.val ha) k)
    simp only [Pi.algebraMap_apply, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem] at this
    exact this.exists.choose_spec
  rwa [← Ideal.mem_bot (R := R), ← Ideal.iInf_pow_eq_bot_of_isLocalRing _
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top, Ideal.mem_iInf]
