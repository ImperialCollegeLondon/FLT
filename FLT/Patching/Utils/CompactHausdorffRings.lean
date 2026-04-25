module

public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.GroupTheory.Divisible
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Algebra.Ring.Ideal

@[expose] public section

section CompactHausdorff

/-- A connected compact Hausdorff vector space over `𝔽_p` is trivial. This might sound easy, but it
seems to require the fact that every nontrivial compact hausdorff group has a nontrivial continuous
character. This fact is a special case of Pontryagin duality, and also a consequence of the
Peter-Weyl theorem. This fact is being worked on at `YaelDillies/mean-fourier`.

Here's a proof of the theorem, using this fact that nontrivial groups have nontrivial characters:
If `χ : A → circle` is a continuous character, then the image of `χ` is connected but is a
subgroup of the `p`th roots of unity, hence must be trivial. Thus, `A` has no nontrivial continuous
characters, so `A` must be trivial. -/
@[to_additive]
theorem Group.subsingleton_of_pow_prime_eq_one
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [ConnectedSpace A] [CompactSpace A] [T2Space A]
    (p : ℕ) (hp : p.Prime) (hAp : ∀ a : A, a ^ p = 1) :
    Subsingleton A := by
  sorry

/-- A compact Hausdorff vector space over `𝔽_p` is totally disconnected. -/
@[to_additive]
theorem Group.totallyDisconnected_of_pow_prime_eq_one
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] (p : ℕ) (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) :
    TotallyDisconnectedSpace A := by
  have : ConnectedSpace (Subgroup.connectedComponentOfOne A) :=
    Subtype.connectedSpace isConnected_connectedComponent
  have : CompactSpace (Subgroup.connectedComponentOfOne A) :=
    isCompact_iff_compactSpace.mp (isClosed_connectedComponent.isCompact)
  have := subsingleton_of_pow_prime_eq_one (Subgroup.connectedComponentOfOne A) p hp
    fun a ↦ Subtype.ext (hA a)
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  exact ((Set.subsingleton_coe _).mp this).eq_singleton_of_mem mem_connectedComponent

/-- A connected compact Hausdorff abelian topological group is divisible. -/
@[to_additive /-- A connected compact Hausdorff abelian topological group is divisible. -/,
  implicit_reducible]
noncomputable def Group.rootable
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [ConnectedSpace A] [CompactSpace A] [T2Space A] : RootableBy A ℕ := by
  apply rootableByOfPowLeftSurj
  suffices ∀ p : ℕ, p.Prime → Function.Surjective fun a : A ↦ a ^ p by
    apply Nat.prime_composite_induction
    · simp
    · simpa using Function.surjective_id
    · grind
    · intro a _ ha b _ hb _
      simp only [pow_mul]
      exact (hb (by grind)).comp (ha (by grind))
  intro p hp
  let f : A →* A := powMonoidHom p
  change Function.Surjective f
  have hf : ∀ a : A ⧸ f.range, a ^ p = 1 := by
    intro a
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨a, rfl⟩
  have : IsClosed (f.range : Set A) := (isCompact_range (continuous_pow p)).isClosed
  have := totallyDisconnected_of_pow_prime_eq_one (A ⧸ f.range) p hp hf
  have : ConnectedSpace (A ⧸ f.range) :=
    QuotientGroup.mk_surjective.connectedSpace QuotientGroup.continuous_mk
  rw [← MonoidHom.range_eq_top, ← QuotientGroup.subsingleton_iff]
  exact subsingleton_of_preconnected_totallyDisconnected

/-- A connected compact Hausdorff abelian topological group does not admit a nontrivial compact
group of automorphisms. -/
@[to_additive]
theorem CommGroup.no_compact_automorphisms
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [ConnectedSpace A] [CompactSpace A] [T2Space A] (K : Subgroup (ContinuousMonoidHom A A))
    (hK : IsCompact (K : Set (ContinuousMonoidHom A A))) :
    K = ⊥ := by
  have A_rootable : RootableBy A ℕ := Group.rootable A
  rw [eq_bot_iff]
  intro f hf
  ext a
  rw [ContinuousMonoidHom.one_toFun]
  by_contra! ha
  let U : Set A := {f a}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  have hU1 : 1 ∈ U := ha.symm
  let W : Set (A →ₜ* A) := {f | Set.MapsTo f Set.univ U}
  have hW : IsOpen W :=
    (ContinuousMonoidHom.isInducing_toContinuousMap A A).continuous.isOpen_preimage _
      (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hU)
  have hW1 : 1 ∈ W := by simpa [W]
  replace hW1 : W ∈ nhds 1 := hW.mem_nhds hW1
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨n, hn0, hnf⟩ :=
    (mapClusterPt_iff_frequently.mp (mapClusterPt_one_atTop_pow ⟨f, hf⟩) (Subtype.val ⁻¹' W)
    (continuousAt_subtype_val.preimage_mem_nhds (by exact hW1))).forall_exists_of_atTop 1
  replace hn0 : n ≠ 0 := by grind
  rw [Set.mem_preimage, Subgroup.coe_pow, Subtype.coe_mk,
    Set.mem_setOf_eq, Set.mapsTo_univ_iff, ← Set.range_subset_iff] at hnf
  change (f ^ n).range ≤ U at hnf
  suffices f.range ≤ (f ^ n).range by
    exact (Set.Subset.trans this hnf) ⟨a, rfl⟩ rfl
  rintro - ⟨b, rfl⟩
  use RootableBy.root b n
  simp [ContinuousMonoidHom.pow_apply, ← map_pow, RootableBy.root_cancel b hn0]

/-- A compact Hausdorff ring is totally disconnected. -/
instance {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] : TotallyDisconnectedSpace R := by
  let C₀ : Ideal R := Ideal.connectedComponentOfZero R
  suffices C₀ = ⊥ from
    totallyDisconnectedSpace_iff_connectedComponent_zero.mpr (SetLike.ext'_iff.mp this)
  have C₀_isClosed : IsClosed (C₀ : Set R) := isClosed_connectedComponent
  have C₀_isCompact : IsCompact (C₀ : Set R) := C₀_isClosed.isCompact
  have : CompactSpace C₀ := isCompact_iff_compactSpace.mp C₀_isCompact
  have C₀_isConnected : IsConnected (C₀ : Set R) := isConnected_connectedComponent
  have : ConnectedSpace C₀ := isConnected_iff_connectedSpace.mp C₀_isConnected
  let f : ContinuousAddMonoidHom R (ContinuousAddMonoidHom C₀ C₀) :=
  { toFun r :=
    { toFun := fun c ↦ r • c
      map_zero' := by simp
      map_add' := by simp [smul_add]
      continuous_toFun := by fun_prop }
    map_zero' := by apply DFunLike.ext; intros; apply zero_smul
    map_add' := by intros; apply DFunLike.ext; intros; apply add_smul
    continuous_toFun := ContinuousAddMonoidHom.continuous_of_continuous_uncurry _ continuous_smul }
  have key := AddCommGroup.no_compact_automorphisms f.range (isCompact_range f.continuous)
  refine eq_bot_iff.mpr fun c hc ↦ ?_
  replace key : f.toAddMonoidHom 1 ⟨c, hc⟩ = (0 : ContinuousAddMonoidHom C₀ C₀) ⟨c, hc⟩ := by
    rw [AddMonoidHom.range_eq_bot_iff.mp key, AddMonoidHom.zero_apply]
  exact (one_smul R c).symm.trans (Subtype.ext_iff.mp key)

end CompactHausdorff
