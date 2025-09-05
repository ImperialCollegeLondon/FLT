import Mathlib.Topology.Constructions

theorem DiscretePi {X Y : Type*} [TopologicalSpace Y] (f : X → Y) (n : ℕ)
    (h : ∀ (x : X), ∃ U, IsOpen U ∧ f ⁻¹' U = {x}) (x' : Fin n → X) :
    (∃ U' : Set (Fin n → Y), IsOpen U' ∧
    (fun (t : Fin n → X) (i : Fin n) ↦ f (t i))⁻¹' U' = {x'}) := by
  have h (i : Fin n) := h (x' i)
  use Set.pi (Set.univ) (fun (i : Fin n) => Classical.choose (h i))
  refine ⟨isOpen_set_pi Set.finite_univ fun a _ ↦ (Classical.choose_spec (h a)).1, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_singleton_iff]
  constructor
  · intro hy
    ext t
    specialize hy t
    have H := (Classical.choose_spec (h t)).2
    rw [← Set.mem_preimage] at hy
    simp_all only [Set.mem_singleton_iff]
  · intro eq i
    have H := (Classical.choose_spec (h i)).2
    refine Set.mem_preimage.mp (by simp_all only [Set.mem_singleton_iff])

theorem HomeoDiscrete_of_Discrete {X Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (h : Y ≃ₜ Y') (H : ∀ (x : X), ∃ U, IsOpen U ∧ f ⁻¹' U = {x}) (x : X) :
    (∃ U' : Set Y', IsOpen U' ∧ (h ∘ f)⁻¹' U' = {x}) := by
  obtain ⟨U, Uopen, Ueq⟩ := H x
  use h '' U
  refine ⟨(Homeomorph.isOpen_image h).mpr Uopen, ?_⟩
  ext y
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_image, EmbeddingLike.apply_eq_iff_eq,
    exists_eq_right, Set.mem_singleton_iff]
  constructor
  · intro incl
    simpa [← Set.mem_preimage, Ueq] using incl
  · intro eq
    simp [eq, ← Set.mem_preimage, Ueq]

theorem Discrete_of_HomeoDiscrete {X Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (h : Y ≃ₜ Y') (H : ∀ (x : X), ∃ U', IsOpen U' ∧ ⇑h ∘ f ⁻¹' U' = {x}) (x : X) :
    (∃ U : Set Y, IsOpen U ∧  f⁻¹' U = {x}) := by
  obtain ⟨U, Uopen, Ueq⟩ := H x
  use h.symm '' U
  refine ⟨(Homeomorph.isOpen_image h.symm).mpr Uopen, ?_⟩
  ext y
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · intro ⟨t, ht1, ht2⟩
    suffices y ∈ ⇑h ∘ f ⁻¹' U by
      simpa [Ueq]
    simpa [← ht2]
  · intro eq
    use h (f x)
    exact ⟨by simp [← Set.mem_preimage, ← Set.preimage_comp, Ueq], by simp [eq]⟩

theorem HomeoDiscrete_iff_Discrete {X Y Y' : Type*} [TopologicalSpace Y]
    [TopologicalSpace Y'] (f : X → Y) (h : Y ≃ₜ Y') :
    (∀ x : X, ∃ U : Set Y, IsOpen U ∧  f⁻¹' U = {x}) ↔
    (∀ x : X, ∃ U' : Set Y', IsOpen U' ∧ (h ∘ f)⁻¹' U' = {x}) :=
  ⟨HomeoDiscrete_of_Discrete f h, Discrete_of_HomeoDiscrete f h⟩

theorem HomDiscrete_of_Discrete {X X' Y : Type*} [TopologicalSpace Y] (f : X → Y)
    (h : X ≃ X') (H : ∀ (x : X), ∃ U, IsOpen U ∧ f ⁻¹' U = {x}) (x : X') :
    (∃ U' : Set Y, IsOpen U' ∧ h '' (f ⁻¹' U') = {x}):= by
  obtain ⟨U, Uopen, Ueq⟩ := H (h.symm x)
  exact ⟨U, Uopen, by simp [Ueq]⟩

theorem Discrete_of_HomDiscrete {X X' Y : Type*} [TopologicalSpace Y] (f : X → Y)
    (h : X ≃ X') (H : ∀ (x' : X'), ∃ U', IsOpen U' ∧ ⇑h '' (f ⁻¹' U') = {x'}) (x : X) :
    (∃ U : Set Y, IsOpen U ∧  f⁻¹' U = {x}) := by
  obtain ⟨U, Uopen, Ueq⟩ := H (h x)
  refine ⟨U, Uopen, ?_⟩
  simp_rw [(Equiv.eq_preimage_iff_image_eq h (f ⁻¹' U) {h x}).mpr Ueq,
    Equiv.preimage_eq_iff_eq_image, Set.image_singleton]

theorem HomDiscrete_iff_Discrete {X X' Y : Type*} [TopologicalSpace Y] (f : X → Y)
    (h : X ≃ X') : (∀ x' : X', ∃ U' : Set Y, IsOpen U' ∧ h '' (f ⁻¹' U') = {x'}) ↔
    (∀ x : X, ∃ U : Set Y, IsOpen U ∧  f⁻¹' U = {x}) :=
  ⟨Discrete_of_HomDiscrete f h, HomDiscrete_of_Discrete f h⟩


-- following maybe should be in the topology.order file (home of discrete topology)

lemma inter_Discrete {A : Type*} [TopologicalSpace A] (X Y : Set A)
    [DiscreteTopology X] : DiscreteTopology ↑(Y ∩ X) := by
  refine singletons_open_iff_discrete.mp ?_
  intro ⟨a, InY, InX⟩
  refine isOpen_mk.mpr ?_
  have h : DiscreteTopology ↑X := inferInstance
  apply (singletons_open_iff_discrete).mpr at h
  obtain ⟨U, Uopen, Ueq⟩ := h ⟨a, InX⟩
  refine ⟨U, Uopen, ?_⟩
  rw [Set.eq_singleton_iff_unique_mem] at Ueq
  aesop

lemma Discrete_inter {A : Type*} [TopologicalSpace A] (X Y : Set A)
    [DiscreteTopology X] : DiscreteTopology ↑(X ∩ Y) := by
  rw [Set.inter_comm]
  exact inter_Discrete X Y
