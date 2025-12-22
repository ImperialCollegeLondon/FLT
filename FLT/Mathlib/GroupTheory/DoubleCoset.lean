import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Algebra.Group.Subgroup.Actions
import FLT.Mathlib.Topology.Algebra.Group.Quotient

lemma DoubleCoset.mem_quotTodoubleCoset_iff {G : Type*} [Group G] (H K : Subgroup G)
    (i : Quotient (H : Set G) K) (g : G) : g ∈ quotToDoubleCoset H K i ↔ mk H K g = i := by
  constructor
  · intro hg
    simp_rw [mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hg), Quotient.out_eq]
  · intro hg
    rw [← out_eq' _ _ i] at hg
    exact mem_doubleCoset.mpr ((eq _ _ _ g).mp hg.symm)

theorem DoubleCoset.iUnion_finset_quotTodoubleCoset {G : Type*} [Group G] (H K : Subgroup G) :
    (∃ I : Finset (Quotient (H : Set G) K), ⋃ i ∈ I, quotToDoubleCoset H K i = .univ) ↔
    Finite (Quotient (H : Set G) K) := by
  constructor
  · intro ⟨I, hI⟩
    suffices (I : Set (Quotient (H : Set G) K)) = Set.univ by
      rw [← Set.finite_univ_iff, ← this]
      exact I.finite_toSet
    rw [Set.eq_univ_iff_forall] at hI ⊢
    rintro ⟨g⟩
    obtain ⟨_, ⟨i, _, rfl⟩, T, ⟨hi, rfl⟩, hT : g ∈ quotToDoubleCoset H K i⟩ := hI g
    rw [DoubleCoset.mem_quotTodoubleCoset_iff] at hT
    simpa [← hT] using hi
  · intro _
    cases nonempty_fintype (Quotient (H : Set G) K)
    use Finset.univ
    simpa using DoubleCoset.union_quotToDoubleCoset H K

theorem DoubleCoset.union_image_mk_rightRel {G : Type*} [Group G] (H K : Subgroup G) :
    ⋃ (q : DoubleCoset.Quotient H K), Quot.mk (QuotientGroup.rightRel H) ''
    (doubleCoset (Quotient.out q : G) H K) = Set.univ := by
  have Cover_Dfx := DoubleCoset.union_quotToDoubleCoset H K
  refine Eq.symm (Set.Subset.antisymm ?_ fun ⦃a⦄ a ↦ trivial)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image]
  obtain ⟨y, hy⟩ := Quot.exists_rep x
  have ⟨i, hi⟩ : ∃ i : DoubleCoset.Quotient H K,
      y ∈ doubleCoset (Quotient.out i) H K  := by
    contrapose Cover_Dfx
    refine (Set.ne_univ_iff_exists_notMem (⋃ q, quotToDoubleCoset H K q)).mpr ?_
    exact ⟨y, by simpa using Cover_Dfx⟩
  exact ⟨i, y, hi, hy⟩

theorem DoubleCoset.isOpen_doubleCoset {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : DoubleCoset.Quotient H K) :
    IsOpen (X := G) (doubleCoset (Quotient.out i) H K) := by
  simpa only [doubleCoset] using (IsOpen.mul_left hK)

theorem DoubleCoset.isOpen_doubleCoset_rightrel_mk {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : DoubleCoset.Quotient H K) :
    IsOpen (Quot.mk ⇑(QuotientGroup.rightRel H) '' doubleCoset (Quotient.out i) H K) := by
  apply (QuotientGroup.isOpenQuotientMap_rightrel_mk H).isOpenMap
  exact DoubleCoset.isOpen_doubleCoset H K hK i

theorem DoubleCoset.union_finset_rightrel_cover {G : Type*} [Group G] (H K : Subgroup G)
    (t : Finset (Quotient H (K : Set G))) (ht : Set.univ ⊆ ⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.rightRel H) '' doubleCoset (Quotient.out i)
    H K) : ⋃ q ∈ t, doubleCoset (Quotient.out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem (⋃ q ∈ t,
    doubleCoset (Quotient.out q) H K)).mp ht
  refine (Set.ne_univ_iff_exists_notMem (⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.rightRel H) '' doubleCoset (Quotient.out i)
    H K)).mpr ⟨Quot.mk (⇑(QuotientGroup.rightRel H)) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨y, hy, ?_⟩
  rw [← doubleCoset_eq_of_mem hq]
  apply mem_doubleCoset.mpr
  obtain ⟨a, ha⟩ : ∃ a : H, x = a * q := by
    obtain ⟨a, ha⟩  : ∃ a : H, a * x = q := by
      obtain ⟨a', ha'⟩ := (Quotient.eq).mp hx
      refine ⟨a', by simpa using ha'⟩
    exact ⟨⟨ a⁻¹, by simp only [inv_mem_iff, SetLike.coe_mem]⟩, eq_inv_mul_of_mul_eq ha⟩
  refine ⟨a.1, ?_⟩
  simp only [Subtype.coe_prop, SetLike.mem_coe, true_and]
  exact ⟨1, Subgroup.one_mem K, by simpa using ha⟩
