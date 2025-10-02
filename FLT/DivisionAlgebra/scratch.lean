import Mathlib

-- scrath file where I work on iso₁_cont_extracted in max(?) generality

variable (R S : Type*) [Ring R] [Ring S] [TopologicalSpace R] [TopologicalSpace S]
variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
  [TopologicalSpace M] [IsModuleTopology R M] [TopologicalSpace N] [IsModuleTopology S N]


instance : Module (Prod R S) (Prod M N) := by
  -- i need to do this first
  sorry

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

lemma perm_map_cont : Continuous (perm_map R S M N) := by

  sorry -- where does this come in??

def hmm : (R × M) × (S × N) → (M × N) :=
  fun a => (a.1.1 • a.1.2, a.2.1 • a.2.2)

lemma smul_cont : ContinuousSMul (Prod R S) (Prod M N) := by
  refine { continuous_smul := ?_ }
  rw [@continuous_prodMk]

  have : (fun p ↦ p.1 • p.2 : (R × S) × M × N → M × N) = (hmm R S M N) ∘ (perm_map R S M N) := by
    ext a
    all_goals simp only [Function.comp_apply]
    all_goals rw [perm_map, hmm]
    · simp only

      -- is this not true?
      sorry
    · simp only
      sorry
  rw [this]
  -- refine Continuous.comp ..

  sorry

abbrev incl1 : M → Prod M N :=
  fun a => (a, 0)

abbrev incl2 : N → Prod M N :=
  fun b => (0 , b)

lemma incl1_cont : @Continuous M (M × N) (moduleTopology R M) (moduleTopology (R × S) (M × N))
    (incl1 M N) := by

  sorry

omit [TopologicalSpace M] [TopologicalSpace N] in
lemma id_equals : @id (M × N) = ((incl1 M N) ∘ (Prod.fst)) + ((incl2 M N) ∘ (Prod.snd)) := by
  ext a
  all_goals simp

--- this will be the final goal
lemma Final : IsModuleTopology (Prod R S) (Prod M N) := by
  have h1 := add_cont R S M N
  have h2 := smul_cont R S M N
  refine IsModuleTopology.of_continuous_id ?_
  rw [id_equals]
  -- I need to rewrite the topological spaces in a and b!!
  -- is a now in the correct form?
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
    · -- to do; should be a mirror of the proof for incl1_cont
      sorry
    · convert @continuous_snd M N (moduleTopology R M) (moduleTopology S N)
      all_goals exact IsModuleTopology.eq_moduleTopology' -- as before?
  exact @Continuous.add _ (moduleTopology (R × S) (M × N)) _
    (ModuleTopology.continuousAdd (R × S) (M × N)) _ _ _ _  a b
