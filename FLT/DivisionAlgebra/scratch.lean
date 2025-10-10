import Mathlib

variable (R S : Type*) [Ring R] [Ring S] [TopologicalSpace R] [TopologicalSpace S] (M N : Type*)
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] [TopologicalSpace M]
  [IsModuleTopology R M] [TopologicalSpace N] [IsModuleTopology S N]

instance prodHSMul : HSMul (R × S) (M × N) (M × N) where
  hSMul a b := (a.1 • b.1, a.2 • b.2) -- why is this needed...

-- maybe there is an easier way to do this without being explicit?
local instance nameme : Module (Prod R S) (Prod M N) where
  smul a b := (a.1 • b.1, a.2 • b.2)
  one_smul a := by
    have : (1 : (R × S)) • a= ((1 : R × S).1 • a.1, (1 : R × S).2 • a.2) := by
      rfl
    aesop
  mul_smul a b c := by
    have : (a * b) • c = ((a * b).1 • c.1, (a * b).2 • c.2) := by
      rfl
    simp_rw [this, Prod.fst_mul, Prod.snd_mul, mul_smul]
    rfl
  smul_zero a := by
    have : a • (0 : M × N) = (a.1 • 0, a.2 • 0) := by
      rfl
    aesop
  zero_smul a := by
    have : (0 : R × S) • a = ((0 : R) • a.1, (0 : S) • a.2) := by
      rfl
    aesop
  smul_add a b c:= by
    have : a • (b + c) = (a.1 • (b + c).1, a.2 • (b + c).2) := by
      rfl
    aesop
  add_smul a b c := by
    have : (a + b) • c = ((a + b).1 • c.1, (a + b).2 • c.2) := by
      rfl
    simp_rw [this, Prod.fst_add, Prod.snd_add, add_smul]
    rfl

-- please tell me why I need to add everything in here...
lemma add_cont (R S : Type*) [Ring R] [Ring S] [TopologicalSpace R] [TopologicalSpace S]
    (M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] [TopologicalSpace M]
    [IsModuleTopology R M] [TopologicalSpace N] [IsModuleTopology S N] :
    ContinuousAdd (Prod M N) := by
  have a : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  have b : ContinuousAdd N := IsModuleTopology.toContinuousAdd S N
  exact Prod.continuousAdd

def perm_map : (R × S) × (M × N) → (R × M) × (S × N) :=
  fun a => ((a.1.1, a.2.1), (a.1.2, a.2.2))

omit [Ring R] [Ring S] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
  [IsModuleTopology R M] [IsModuleTopology S N] in
lemma perm_map_cont : Continuous (perm_map R S M N) := by
  unfold perm_map
  simp only [continuous_prodMk]
  constructor
  <;> constructor
  <;> refine Continuous.comp ?_ ?_
  all_goals try exact continuous_fst
  all_goals try exact continuous_snd

def prod_smul : (R × M) × (S × N) → (M × N) :=
  Prod.map (fun (r, m) => r • m) (fun (s, n) => s • n)

lemma smul_cont : ContinuousSMul (Prod R S) (Prod M N) := by
  refine { continuous_smul := ?_ }
  have : (fun p ↦ p.1 • p.2 : (R × S) × M × N → M × N) =
      (prod_smul R S M N) ∘ (perm_map R S M N) := by
    ext a
    all_goals simp only [Function.comp_apply, perm_map, prod_smul]
    all_goals rfl
  rw [this]
  refine Continuous.comp ?_ (perm_map_cont R S M N)
  · apply Continuous.prodMap
    all_goals exact ContinuousSMul.continuous_smul

abbrev incl1 : M → Prod M N :=
  fun a => (a, 0)

abbrev incl2 : N → Prod M N :=
  fun b => (0 , b)

-- almost certainly can and should be extracting all the maps from the proofs of add and smul

lemma induced_add_cont : @ContinuousAdd M
    (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))) _ := by
  suffices h : @Continuous (M × M) (M × N) (@instTopologicalSpaceProd M M
      (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))
      (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))))
      ((moduleTopology (R × S) (M × N))) (fun (a : M × M) => (a.1 + a.2, (0 : N))) by
    convert (@Topology.IsInducing.continuous_iff (M × M) M (M × N) (fun (a : M × M) ↦ a.1 + a.2)
        (incl1 M N) (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))
        (@instTopologicalSpaceProd M M
        (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))
        (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))))
        (moduleTopology (R × S) (M × N)) _).mpr h
    · constructor <;> intro h
      · exact ContinuousAdd.continuous_add
      · rw [continuous_def] at h
        use h
    · rw [@Topology.isInducing_iff]
  have h : (fun (a : M × M) => (a.1 + a.2, (0 : N))) =
      (fun (b : (M × N) × (M × N)) => (b.1.1 + b.2.1, b.1.2 + b.2.2)) ∘
      (fun (a : M × M ) => (((a.1, 0) : (M × N)) , (((a.2, 0)) : (M × N)))) := by
    ext a
    all_goals simp
  rw [h]
  refine @Continuous.comp (M × M) ((M × N) × M × N) (M × N) (@instTopologicalSpaceProd M M
    (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))
    (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))))
    (@instTopologicalSpaceProd (M × N) (M × N) (moduleTopology (R × S) (M × N))
    (moduleTopology (R × S) (M × N))) (moduleTopology (R × S) (M × N))
    (f := (fun (a : M × M ) => (((a.1, 0) : (M × N)) , (((a.2, 0)) : (M × N)))))
    (g := (fun (b : (M × N) × (M × N)) => (b.1.1 + b.2.1, b.1.2 + b.2.2))) ?_ ?_
  · convert ContinuousAdd.continuous_add
    exact ModuleTopology.continuousAdd (R × S) (M × N)
  · refine @Continuous.prodMap (M × N) (M × N) M M (moduleTopology (R × S) (M × N))
      (moduleTopology (R × S) (M × N))
      (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))
      (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))
      (f := incl1 M N) (g := incl1 M N) ?_ ?_
    all_goals exact continuous_iff_le_induced.mpr fun U a ↦ a

lemma induced_smul_cont : @ContinuousSMul R M _ _
    (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))) := by
  suffices h : @Continuous (R × M) (M × N) (@instTopologicalSpaceProd R M _
      (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))))
      ((moduleTopology (R × S) (M × N))) (fun (a : R × M) => (a.1 • a.2, (0 : N))) by
    convert (@Topology.IsInducing.continuous_iff (R × M) M (M × N) (fun (a : R × M) ↦ a.1 • a.2)
        (incl1 M N) (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))
        (@instTopologicalSpaceProd R M _
        (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))))
        (moduleTopology (R × S) (M × N)) _).mpr h
    · constructor <;> intro h
      · exact ContinuousSMul.continuous_smul
      · rw [continuous_def] at h
        use h
    · rw [@Topology.isInducing_iff]
  have : (fun (a : R × M) ↦ (a.1 • a.2, 0)) =
      (fun (c : (R × S) × (M × N)) => (c.1.1 • c.2.1, c.1.2 • c.2.2)) ∘
      (fun (b : R × M × N) => ((b.1, (0 : S)), (b.2.1, b.2.2))) ∘
      (fun (a : R × M) => (a.1, a.2, (0 : N))) := by
    ext a
    · rfl
    · simp only [Prod.mk.eta, Function.comp_apply, smul_zero]
  rw [this]
  refine @Continuous.comp (R × M) ((R × S) × M × N) (M × N) (@instTopologicalSpaceProd R M _
    (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))))
    (@instTopologicalSpaceProd (R × S) (M × N) _ (moduleTopology (R × S) (M × N)))
    (moduleTopology (R × S) (M × N))
    (f := (fun (b : R × M × N) => ((b.1, (0 : S)), (b.2.1, b.2.2))) ∘
      (fun (a : R × M) => (a.1, a.2, (0 : N))))
    (g := (fun (c : (R × S) × (M × N)) => (c.1.1 • c.2.1, c.1.2 • c.2.2))) ?_ ?_
  · exact ContinuousSMul.continuous_smul
  · refine @Continuous.comp (R × M) (R × M × N) ((R × S) × M × N) (@instTopologicalSpaceProd R M _
      (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))))
      (@instTopologicalSpaceProd R (M × N) _ (moduleTopology (R × S) (M × N)))
      (@instTopologicalSpaceProd (R × S) (M × N) _ (moduleTopology (R × S) (M × N)))
      (f := (fun (a : R × M) => (a.1, a.2, (0 : N))))
      (g := (fun (b : R × M × N) => ((b.1, (0 : S)), (b.2.1, b.2.2)))) ?_ ?_
    · simp only [Prod.mk.eta, continuous_prodMk]
      · constructor
        · constructor
          · exact @continuous_fst R (M × N) _ (moduleTopology (R × S) (M × N))
          · rw [continuous_def] --is there a better way?
            intro s hs
            have : ((fun (x : R × M × N) ↦ 0) ⁻¹' s) = ∅ ∨
                ((fun (x : R × M × N) ↦ 0) ⁻¹' s = Set.univ) := by
              rcases (Classical.em (0 ∈ s)) with h | h
              all_goals aesop
            aesop
        · exact @continuous_snd R (M × N) _ (moduleTopology (R × S) (M × N))
    · simp only [continuous_prodMk]
      constructor
      · exact @continuous_fst R M _
          (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))
      · have : (fun (x : R × M) ↦ (x.2, 0)) = incl1 M N ∘ (fun (x : R × M) => x.2) := by
          rfl
        rw [this]
        refine @Continuous.comp (R × M) M (M × N) (@instTopologicalSpaceProd R M _
          (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N))))
          (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))
          (moduleTopology (R × S) (M × N))
          (f := fun (a : R × M) => a.2) (g := incl1 M N)  ?_ ?_
        · exact continuous_iff_le_induced.mpr fun U a ↦ a
        · exact @continuous_snd R M _
            (TopologicalSpace.induced (incl1 M N) (moduleTopology (R × S) (M × N)))

lemma incl1_cont : @Continuous M (M × N) (moduleTopology R M) (moduleTopology (R × S) (M × N))
    (incl1 M N) := by
  refine continuous_iff_le_induced.mpr ?_
  refine sInf_le ?_
  constructor
  · exact induced_smul_cont R S M N
  · exact induced_add_cont R S M N

lemma induced_add_cont' : @ContinuousAdd N
    (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))) _ := by
  suffices h : @Continuous (N × N) (M × N) (@instTopologicalSpaceProd N N
      (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))
      (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))))
      ((moduleTopology (R × S) (M × N))) (fun (a : N × N) => ((0 : M), a.1 + a.2)) by
    convert (@Topology.IsInducing.continuous_iff (N × N) N (M × N) (fun (a : N × N) ↦ a.1 + a.2)
        (incl2 M N) (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))
        (@instTopologicalSpaceProd N N
        (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))
        (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))))
        (moduleTopology (R × S) (M × N)) _).mpr h
    · constructor <;> intro h
      · exact ContinuousAdd.continuous_add
      · rw [continuous_def] at h
        use h
    · rw [@Topology.isInducing_iff]
  have h : (fun (a : N × N) => ((0 : M), a.1 + a.2)) =
      (fun (b : (M × N) × (M × N)) => (b.1.1 + b.2.1, b.1.2 + b.2.2)) ∘
      (fun (a : N × N ) => (((0, a.1) : (M × N)) , (((0, a.2)) : (M × N)))) := by
    ext a
    all_goals simp
  rw [h]
  refine @Continuous.comp (N × N) ((M × N) × M × N) (M × N) (@instTopologicalSpaceProd N N
    (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))
    (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))))
    (@instTopologicalSpaceProd (M × N) (M × N) (moduleTopology (R × S) (M × N))
    (moduleTopology (R × S) (M × N))) (moduleTopology (R × S) (M × N))
    (f := (fun (a : N × N ) => (((0, a.1) : (M × N)) , (((0, a.2)) : (M × N)))))
    (g := (fun (b : (M × N) × (M × N)) => (b.1.1 + b.2.1, b.1.2 + b.2.2))) ?_ ?_
  · convert ContinuousAdd.continuous_add
    exact ModuleTopology.continuousAdd (R × S) (M × N)
  · refine @Continuous.prodMap (M × N) (M × N) N N (moduleTopology (R × S) (M × N))
      (moduleTopology (R × S) (M × N))
      (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))
      (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))
      (f := incl2 M N) (g := incl2 M N) ?_ ?_
    all_goals exact continuous_iff_le_induced.mpr fun U a ↦ a

lemma induced_smul_cont' : @ContinuousSMul S N _ _
    (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))) := by
  suffices h : @Continuous (S × N) (M × N) (@instTopologicalSpaceProd S N _
      (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))))
      ((moduleTopology (R × S) (M × N))) (fun (a : S × N) => ((0 : M), a.1 • a.2)) by
    convert (@Topology.IsInducing.continuous_iff (S × N) N (M × N) (fun (a : S × N) ↦ a.1 • a.2)
        (incl2 M N) (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))
        (@instTopologicalSpaceProd S N _
        (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))))
        (moduleTopology (R × S) (M × N)) _).mpr h
    · constructor <;> intro h
      · exact ContinuousSMul.continuous_smul
      · rw [continuous_def] at h
        use h
    · rw [@Topology.isInducing_iff]
  have : (fun (a : S × N) ↦ (0, a.1 • a.2)) =
      (fun (c : (R × S) × (M × N)) => (c.1.1 • c.2.1, c.1.2 • c.2.2)) ∘
      (fun (b : S × M × N) => (((0 : R), b.1), (b.2.1, b.2.2))) ∘
      (fun (a : S × N) => (a.1, (0 : M), a.2)) := by
    ext a
    · aesop
    · simp only [Prod.mk.eta, Function.comp_apply, smul_zero]
  rw [this]
  refine @Continuous.comp (S × N) ((R × S) × M × N) (M × N) (@instTopologicalSpaceProd S N _
    (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))))
    (@instTopologicalSpaceProd (R × S) (M × N) _ (moduleTopology (R × S) (M × N)))
    (moduleTopology (R × S) (M × N))
    (f := (fun (b : S × M × N) => (((0 : R), b.1), (b.2.1, b.2.2))) ∘
      (fun (a : S × N) => (a.1, (0 : M), a.2)))
    (g := (fun (c : (R × S) × (M × N)) => (c.1.1 • c.2.1, c.1.2 • c.2.2))) ?_ ?_
  · exact ContinuousSMul.continuous_smul
  · refine @Continuous.comp (S × N) (S × M × N) ((R × S) × M × N) (@instTopologicalSpaceProd S N _
      (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))))
      (@instTopologicalSpaceProd S (M × N) _ (moduleTopology (R × S) (M × N)))
      (@instTopologicalSpaceProd (R × S) (M × N) _ (moduleTopology (R × S) (M × N)))
      (f := (fun (a : S × N) => (a.1, (0 : M), a.2)))
      (g := (fun (b : S × M × N) => (((0 : R), b.1), (b.2.1, b.2.2)))) ?_ ?_
    · simp only [Prod.mk.eta, continuous_prodMk]
      · constructor
        · constructor
          · rw [continuous_def]
            intro s hs
            have : ((fun (x : S × M × N) ↦ 0) ⁻¹' s) = ∅ ∨
                ((fun (x : S × M × N) ↦ 0) ⁻¹' s = Set.univ) := by
              rcases (Classical.em (0 ∈ s)) with h | h
              all_goals aesop
            aesop
          · exact @continuous_fst S (M × N) _ (moduleTopology (R × S) (M × N))
        · exact @continuous_snd S (M × N) _ (moduleTopology (R × S) (M × N))
    · simp only [continuous_prodMk]
      constructor
      · exact @continuous_fst S N _
          (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))
      · have : (fun (x : S × N) ↦ (0, x.2)) = incl2 M N ∘ (fun (x : S × N) => x.2) := by
          rfl
        rw [this]
        refine @Continuous.comp (S × N) N (M × N) (@instTopologicalSpaceProd S N _
          (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N))))
          (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))
          (moduleTopology (R × S) (M × N))
          (f := fun (a : S × N) => a.2) (g := incl2 M N)  ?_ ?_
        · exact continuous_iff_le_induced.mpr fun U a ↦ a
        · exact @continuous_snd S N _
            (TopologicalSpace.induced (incl2 M N) (moduleTopology (R × S) (M × N)))

lemma incl2_cont : @Continuous N (M × N) (moduleTopology S N) (moduleTopology (R × S) (M × N))
    (incl2 M N) := by
  refine continuous_iff_le_induced.mpr ?_
  refine sInf_le ?_
  constructor
  · exact induced_smul_cont' R S M N
  · exact induced_add_cont' R S M N

/-
Ideally I would like to have this proved by just using the fact incl1 is continuous and use
continuous composition with a swap function - the problem is this requires product topologies...
which is kinda the whole point of these theorems.
-/

omit [TopologicalSpace M] [TopologicalSpace N] in
lemma id_equals : @id (M × N) = ((incl1 M N) ∘ (Prod.fst)) + ((incl2 M N) ∘ (Prod.snd)) := by
  ext a
  all_goals simp

lemma Final : IsModuleTopology (Prod R S) (Prod M N) := by
  have h1 := add_cont R S M N
  have h2 := smul_cont R S M N
  refine IsModuleTopology.of_continuous_id ?_
  rw [id_equals]
  have a : @Continuous (Prod M N) (Prod M N) instTopologicalSpaceProd
      (moduleTopology (R × S) (M × N)) ((incl1 M N) ∘ (Prod.fst)) := by
    refine @Continuous.comp (Prod M N) M (Prod M N) instTopologicalSpaceProd (moduleTopology R M)
      (moduleTopology (R × S) (M × N)) (Prod.fst) (incl1 M N) ?_ ?_
    · exact incl1_cont R S M N
    · convert @continuous_fst M N (moduleTopology R M) (moduleTopology S N)
      all_goals exact IsModuleTopology.eq_moduleTopology' -- maybe I need to be synthesising better?
  have b : @Continuous (Prod M N) (Prod M N) instTopologicalSpaceProd
      (moduleTopology (R × S) (M × N)) ((incl2 M N) ∘ (Prod.snd)) := by
    refine @Continuous.comp (Prod M N) N (Prod M N) instTopologicalSpaceProd (moduleTopology S N)
      (moduleTopology (R × S) (M × N)) (Prod.snd) (incl2 M N) ?_ ?_
    · exact incl2_cont R S M N
    · convert @continuous_snd M N (moduleTopology R M) (moduleTopology S N)
      all_goals exact IsModuleTopology.eq_moduleTopology'
  exact @Continuous.add _ (moduleTopology (R × S) (M × N)) _
    (ModuleTopology.continuousAdd (R × S) (M × N)) _ _ _ _  a b
