import Mathlib

-- scrath file where I work on iso₁_cont_extracted in max(?) generality

variable (R S : Type*) [Ring R] [Ring S] [TopologicalSpace R] [TopologicalSpace S] (M N : Type*)
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] [TopologicalSpace M]
  [IsModuleTopology R M] [TopologicalSpace N] [IsModuleTopology S N]

instance prodHSMul : HSMul (R × S) (M × N) (M × N) where
  hSMul a b := (a.1 • b.1, a.2 • b.2) -- why is this needed...

-- maybe there is an easier way to do this without being explicit?
instance : Module (Prod R S) (Prod M N) where
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
  -- to prove this its the same to prove that the pullback of the (R×S)-module topology is >= than
  -- the R-module topology (as premimages are open in pullback top... so >= → also in moduleTop)

  -- to prove this statement it suffices to show that the pullback topology makes M into a
  -- topological R-module
  -- i.e. smul and add are continuous
  sorry

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
    · -- to do; should be a mirror of the proof for incl1_cont...
      -- or use the proof with a twisting map
      sorry
    · convert @continuous_snd M N (moduleTopology R M) (moduleTopology S N)
      all_goals exact IsModuleTopology.eq_moduleTopology' -- as before?
  exact @Continuous.add _ (moduleTopology (R × S) (M × N)) _
    (ModuleTopology.continuousAdd (R × S) (M × N)) _ _ _ _  a b
