import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.ContinuousMonoidHom

lemma Submonoid.units_isOpen {M : Type*} [TopologicalSpace M] [Monoid M]
  {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

 -- FLT#588
lemma Submonoid.units_isCompact {M : Type*} [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    [T2Space M] {U : Submonoid M} (hU : IsCompact (U : Set M)) : IsCompact (U.units : Set Mˣ) := by
  let φ : Mˣ → M × M := fun x ↦  (↑x, ↑x⁻¹)
  let p : M × M → M := fun (u,v) => u * v
  let q : M × M → M := fun (u,v) => v * u

  have range_φ : p ⁻¹' {1} ∩ q ⁻¹' {1} = Set.range φ := by
    apply Set.ext
    intro (u,v)
    simp_all only[p,q,φ]
    simp_all only [Set.image_univ, Set.mem_range, Prod.mk.injEq,
         Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · -- Forward direction: u * v = 1 ∧ v * u = 1 ⇒ (u, v) ∈ range φ
      intro h
      let y : Mˣ := ⟨u, v, h.1, h.2⟩
      use y
      simp only [Units.inv_mk, and_self, y]
    · -- Backward direction: (u, v) ∈ Set.range φ ⇒ (u * v = 1 ∧ v * u = 1)
      intro h
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      subst left right
      simp_all only [Units.mul_inv, Units.inv_mul, and_self, q, φ, p]

  have closed_range_φ : IsClosed (Set.range φ):= by
    rw [← range_φ]
    exact IsClosed.inter
      (isClosed_singleton.preimage continuous_mul)
      (isClosed_singleton.preimage  (continuous_mul.comp continuous_swap))
  have isCompacthUU : IsCompact ((U : Set M) ×ˢ (U : Set M)) := hU.prod hU

  have φUu_subset : φ '' (U.units : Set Mˣ) ⊆ Set.range φ ∩ U ×ˢ U := by
    rintro z ⟨x, hxU, rfl⟩
    constructor
    · -- φ x ∈ Set.range φ
      simp_all only [SetLike.mem_coe, Set.mem_range, Prod.mk.injEq, p, q, φ]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only [p, q, φ]
    · -- φ x ∈ ↑U ×ˢ ↑U
      simp_all only [SetLike.mem_coe]
      exact hxU
  have subset_φUu : Set.range φ ∩ U ×ˢ U ⊆ φ '' (U.units : Set Mˣ):= by
    intro _ h
    simp_all only [Set.image_univ, Set.mem_range, Set.mem_inter_iff]
    obtain ⟨h1,h2⟩ := h
    rcases h1 with ⟨a,pa⟩
    rw[← pa]
    apply Set.mem_image_of_mem φ
    refine SetLike.mem_coe.mpr ?_
    simp only [ mem_units_iff]
    subst pa
    simp_all only [Set.image_univ,  Set.mem_prod,  SetLike.mem_coe, and_self, φ, p, q]
  have φUu_eq : φ '' (U.units : Set Mˣ) = Set.range φ ∩ U ×ˢ U := by
    exact Eq.symm (Set.Subset.antisymm subset_φUu φUu_subset)

  have φUu_compact : IsCompact (φ '' (U.units : Set Mˣ)) := by
    rw[φUu_eq]
    apply IsCompact.inter_left isCompacthUU closed_range_φ

  let f :  M × M → M × Mᵐᵒᵖ := Prod.map id MulOpposite.op
  have continuous_f : Continuous f:= by
    refine Continuous.prodMap ?_ ?_
    exact continuous_id
    exact MulOpposite.continuous_op
  have f_φ_embedProduct: f ∘ φ = Units.embedProduct M  := by
    ext; simp [f,φ]; simp [f,φ]
  have continuous_φ: Continuous φ := by
    rw [continuous_prodMk]
    constructor
    · exact Units.continuous_val
    · exact Units.continuous_coe_inv
  have isEmbedding_φ : Topology.IsEmbedding φ := by
    apply Topology.IsEmbedding.of_comp continuous_φ continuous_f
    simp only [f_φ_embedProduct]
    exact Units.isEmbedding_embedProduct

  exact (isEmbedding_φ.isCompact_iff).mpr φUu_compact

/-- The monoid homeomorphism between the units of a product of topological monoids
and the product of the units of the monoids.
-/
def ContinuousMulEquiv.piUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)] :
    (Π i, M i)ˣ ≃ₜ* Π i, (M i)ˣ where
  __ := MulEquiv.piUnits
  continuous_toFun := by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
    refine continuous_pi (fun i => ?_)
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · simp only [Function.comp_def, MulEquiv.val_piUnits_apply]
      exact (continuous_apply i).comp' Units.continuous_val
    · simp only [MulEquiv.val_inv_piUnits_apply, Units.inv_eq_val_inv]
      exact (continuous_apply i).comp' Units.continuous_coe_inv
  continuous_invFun :=  by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, MulEquiv.coe_toEquiv_symm]
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_pi (fun i => ?_)
      simp only [Function.comp_def, MulEquiv.val_piUnits_symm_apply]
      exact Units.continuous_val.comp' (continuous_apply i)
    · refine continuous_pi (fun i => ?_)
      simp only [MulEquiv.val_inv_piUnits_symm_apply, Units.inv_eq_val_inv]
      exact Units.continuous_coe_inv.comp' (continuous_apply i)
