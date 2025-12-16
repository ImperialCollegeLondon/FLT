import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.Urysohn

-- https://leanprover.zulipchat.com/#narrow/channel/416277-FLT/topic/Are.20the.20adeles.20Polish.3F/near/563290956

open TopologicalSpace UniformSpace Set Topology

lemma open_of_locally_compact_dense_metrizable {X Y : Type*} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (f : Y → X) (hf : Continuous f) (indf : IsInducing f) (dn : DenseRange f) :
    IsOpen (Set.range f) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [_root_.mem_nhds_iff]
  rw [mem_range] at hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨s, s_op, y_in_s, s_cc⟩ := exists_isOpen_mem_isCompact_closure y
  rw [IsInducing.isOpen_iff indf] at s_op
  obtain ⟨t, t_op, s_preim_t⟩ := s_op
  have clt_im_cls : closure t = closure (f '' s) := by
    rw [Subset.antisymm_iff]
    constructor
    · refine closure_minimal ?_ isClosed_closure
      intro z hz
      rw [mem_closure_iff]
      intro o o_op z_in_o
      unfold DenseRange at dn
      rw [dense_iff_inter_open] at dn
      specialize dn (o ∩ t) (o_op.inter t_op) ⟨z, z_in_o, hz⟩
      grind [image_preimage_eq_inter_range]
grind [closure_mono]
  use t
  refine ⟨?_, t_op, ?_⟩
  · calc
      t ⊆ closure t := subset_closure
      _ = closure (f '' s) := clt_im_cls
      _ ⊆ range f := by
        rw [← closure_image_closure hf]
        have : IsClosed (f '' closure s) := by
          apply IsCompact.isClosed
          exact IsCompact.image s_cc hf
        rw [IsClosed.closure_eq this]
        exact image_subset_range f (closure s)
  · rw [← hy]
    rw [← s_preim_t] at y_in_s
    exact y_in_s

theorem polish_of_locally_compact_second_countable
    (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] [T2Space X]
    [LocallyCompactSpace X] : PolishSpace X := by
  letI _ : MetrizableSpace X := metrizableSpace_of_t3_secondCountable X
  letI _ : MetricSpace X := metrizableSpaceMetric X
  have dn : IsOpen (range (Completion.coe' : X → Completion X)) := by
    apply open_of_locally_compact_dense_metrizable Completion.coe'
    · exact Completion.continuous_coe X
    · exact IsDenseInducing.isInducing Completion.isDenseInducing_coe
    · exact Completion.denseRange_coe
  letI _ : PolishSpace (range (Completion.coe' : X → Completion X)) :=
    IsOpen.polishSpace dn
  have hHomeo : X ≃ₜ range (Completion.coe' : X → Completion X) :=
    (Completion.coe_isometry.isEmbedding).toHomeomorph
  exact hHomeo.isClosedEmbedding.polishSpace
