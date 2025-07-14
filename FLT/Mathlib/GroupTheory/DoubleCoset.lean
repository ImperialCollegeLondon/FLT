import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Algebra.Group.Subgroup.Actions
import FLT.Mathlib.Topology.Algebra.Group.Quotient

lemma Doset.mem_quotToDoset_iff {G : Type*} [Group G] (H K : Subgroup G)
    (i : Quotient (H : Set G) K) (g : G) : g ∈ quotToDoset H K i ↔ mk H K g = i := by
  constructor
  · intro hg
    simp_rw [mk_eq_of_doset_eq (doset_eq_of_mem hg), Quotient.out_eq]
  · intro hg
    rw [← out_eq' _ _ i] at hg
    exact mem_doset.mpr ((eq _ _ _ g).mp hg.symm)

theorem Doset.iUnion_finset_quotToDoset {G : Type*} [Group G] (H K : Subgroup G) :
    (∃ I : Finset (Quotient (H : Set G) K), ⋃ i ∈ I, quotToDoset H K i = .univ) ↔
    Finite (Quotient (H : Set G) K) := by
  constructor
  · intro ⟨I, hI⟩
    suffices (I : Set (Quotient (H : Set G) K)) = Set.univ by
      rw [← Set.finite_univ_iff, ← this]
      exact I.finite_toSet
    rw [Set.eq_univ_iff_forall] at hI ⊢
    rintro ⟨g⟩
    obtain ⟨_, ⟨i, _, rfl⟩, T, ⟨hi, rfl⟩, hT : g ∈ quotToDoset H K i⟩ := hI g
    rw [Doset.mem_quotToDoset_iff] at hT
    simpa [← hT] using hi
  · intro _
    cases nonempty_fintype (Quotient (H : Set G) K)
    use Finset.univ
    simpa using Doset.union_quotToDoset H K

theorem Doset.union_image_mk_rightRel {G : Type*} [Group G] (H K : Subgroup G) :
    ⋃ (q : Doset.Quotient H K), Quot.mk (QuotientGroup.rightRel H) ''
    (Doset.doset (Quotient.out q : G) H K) = Set.univ := by
  have Cover_Dfx := Doset.union_quotToDoset H K
  refine Eq.symm (Set.Subset.antisymm ?_ fun ⦃a⦄ a ↦ trivial)
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image]
  obtain ⟨y, hy⟩ := Quot.exists_rep x
  have ⟨i, hi⟩ : ∃ i : Doset.Quotient H K,
      y ∈ Doset.doset (Quotient.out i) H K  := by
    contrapose Cover_Dfx
    refine (Set.ne_univ_iff_exists_notMem (⋃ q, quotToDoset H K q)).mpr ?_
    exact ⟨y, by simpa using Cover_Dfx⟩
  exact ⟨i, y, hi, hy⟩

theorem Doset.isOpen_doset {G : Type*} [Group G] [tG : TopologicalSpace G] [ContinuousMul G]
    (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : Doset.Quotient H K) :
    @IsOpen G tG (Doset.doset (Quotient.out i) H K) := by
  simpa only [doset] using (IsOpen.mul_left hK)

theorem Doset.isOpen_doset_rightrel_mk {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : Doset.Quotient H K) : IsOpen (Quot.mk
    ⇑(QuotientGroup.rightRel H) '' Doset.doset (Quotient.out i) H K) := by
  apply (QuotientGroup.isOpenQuotientMap_rightrel_mk H).isOpenMap
  exact Doset.isOpen_doset H K hK i

theorem Doset.union_finset_rightrel_cover {G : Type*} [Group G] (H K : Subgroup G)
    (t : Finset (Doset.Quotient H K)) (ht : Set.univ ⊆ ⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.rightRel H) '' Doset.doset (Quotient.out i)
    H K) : ⋃ q ∈ t, Doset.doset (Quotient.out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem (⋃ q ∈ t,
    Doset.doset (Quotient.out q) H K)).mp ht
  refine (Set.ne_univ_iff_exists_notMem (⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.rightRel H) '' Doset.doset (Quotient.out i)
    H K)).mpr ⟨Quot.mk (⇑(QuotientGroup.rightRel H)) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop, not_exists, not_and, not_forall, not_not]
  simp only [not_not] at hx
  refine ⟨y, hy, ?_⟩
  rw [← Doset.doset_eq_of_mem hq]
  apply Doset.mem_doset.mpr
  obtain ⟨a, ha⟩ : ∃ a : H, x = a * q := by
    obtain ⟨a, ha⟩  : ∃ a : H, a * x = q := by
      obtain ⟨a', ha'⟩ := (Quotient.eq).mp hx
      refine ⟨a', by simpa using ha'⟩
    exact ⟨⟨ a⁻¹, by simp only [inv_mem_iff, SetLike.coe_mem]⟩, eq_inv_mul_of_mul_eq ha⟩
  refine ⟨a.1, ?_⟩
  simp only [Subtype.coe_prop, SetLike.mem_coe, true_and]
  exact ⟨1, Subgroup.one_mem K, by simpa using ha⟩
