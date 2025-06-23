import Mathlib.Topology.Algebra.Constructions

@[to_additive]
lemma Units.continuous_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Monoid X] [Monoid Y] {f : X →* Y} (hf : Continuous f) : Continuous (map f) :=
  Units.continuous_iff.mpr ⟨hf.comp continuous_val, hf.comp continuous_coe_inv⟩

open MulOpposite in
@[to_additive]
lemma Units.isOpenMap_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Monoid X] [Monoid Y] {f : X →* Y} (hf_inj : Function.Injective f) (hf : IsOpenMap f) :
    IsOpenMap (map f) := by
  rintro _ ⟨U, hU, rfl⟩
  let g : X × Xᵐᵒᵖ → Y × Yᵐᵒᵖ := Prod.map f (opHomeomorph ∘ f ∘ opHomeomorph.symm)
  have hg_openMap := hf.prodMap <| opHomeomorph.isOpenMap.comp (hf.comp opHomeomorph.symm.isOpenMap)
  refine ⟨g '' U, hg_openMap U hU, Set.ext fun y ↦ ?_⟩
  simp only [embedProduct, OneHom.coe_mk, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
    Prod.map, Prod.exists, MulOpposite.exists, MonoidHom.coe_mk, g]
  refine ⟨fun ⟨a, b, h, ha, hb⟩ ↦ ⟨⟨a, b, hf_inj ?_, hf_inj ?_⟩, ?_⟩,
          fun ⟨x, hxV, hx⟩ ↦ ⟨x, x.inv, by simp [hxV, ← hx]⟩⟩
  all_goals simp_all
