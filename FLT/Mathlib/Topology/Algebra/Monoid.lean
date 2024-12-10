import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Algebra.Monoid

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [ContinuousMul G]
-- TODO: `ContinuousMulConst` would be enough but it doesn't exist, and `ContinuousConstSMul Gᵐᵒᵖ G`
-- should work but doesn't

@[to_additive]
lemma MonoidHom.isOpenMap_of_coinduced (φ : G →* H) (hφcont : Continuous φ)
    (hφcoind : TopologicalSpace.coinduced φ ‹_› = ‹_›) : IsOpenMap φ := by
  intro U hU
  rw [← hφcoind, isOpen_coinduced]
  suffices ⇑φ ⁻¹' (⇑φ '' U) = ⋃ k ∈ φ.ker, (fun x ↦ x * k) ⁻¹' U by
    exact this ▸ isOpen_biUnion (fun k _ ↦ Continuous.isOpen_preimage (by continuity) _ hU)
  ext x
  constructor
  · rintro ⟨y, hyU, hyx⟩
    apply Set.mem_iUnion_of_mem (x⁻¹ * y)
    have : x⁻¹ * y ∈ MonoidHom.ker φ := by simp [mem_ker, hyx]
    simp_all
  · rintro ⟨_, ⟨k, rfl⟩, _, ⟨hk, rfl⟩, hx⟩
    use x * k, hx
    rw [map_mul, hk, mul_one]

-- **TODO** ask Yury how to golf
-- Answer: `IsOpenQuotientMap.prodMap`
open TopologicalSpace in
@[to_additive AddMonoidHom.coinduced_prod_eq_prod_coinduced]
theorem MonoidHom.coinduced_prod_eq_prod_coinduced {X Y S T : Type*} [CommGroup X] [CommGroup Y]
    [CommGroup S] [CommGroup T] (f : X →* S) (g : Y →* T)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [τX : TopologicalSpace X] [ContinuousMul X] [τY : TopologicalSpace Y] [ContinuousMul Y] :
    coinduced (Prod.map f g) instTopologicalSpaceProd =
      @instTopologicalSpaceProd S T (coinduced f τX) (coinduced g τY) := by
  ext U
  rw [@isOpen_prod_iff, isOpen_coinduced, isOpen_prod_iff]
  constructor
  · intro h s t hst
    obtain ⟨x, rfl⟩ := hf s
    obtain ⟨y, rfl⟩ := hg t
    obtain ⟨V1, V2, hV1, hV2, hx1, hy2, h12⟩ := h x y hst
    use f '' V1, g '' V2,
      @MonoidHom.isOpenMap_of_coinduced _ _ _ _ _ (_) _ f (by rw [continuous_iff_coinduced_le])
        rfl V1 hV1,
      @MonoidHom.isOpenMap_of_coinduced _ _ _ _ _ (_) _ g (by rw [continuous_iff_coinduced_le])
        rfl V2 hV2,
      ⟨x, hx1, rfl⟩, ⟨y, hy2, rfl⟩
    rintro ⟨s, t⟩ ⟨⟨x', hx', rfl⟩, ⟨y', hy', rfl⟩⟩
    exact @h12 (x', y') ⟨hx', hy'⟩
  · intro h x y hxy
    rw [Set.mem_preimage, Prod.map_apply] at hxy
    obtain ⟨U1, U2, hU1, hU2, hx1, hy2, h12⟩ := h (f x) (g y) hxy
    exact ⟨f ⁻¹' U1, g ⁻¹' U2, hU1, hU2, hx1, hy2, fun ⟨x', y'⟩ ⟨hx', hy'⟩ ↦ h12 ⟨hx', hy'⟩⟩

section induced

variable {R : Type*} [τR : TopologicalSpace R]
variable {A : Type*} [SMul R A]
variable {S : Type*} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)
variable {B : Type*} [SMul S B]

open Topology

-- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B
@[to_additive]
theorem induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] (g : B →ₑ[f] A)
    (hf : Continuous f) : @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
  convert IsInducing.continuousSMul (IsInducing.induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

@[to_additive]
theorem induced_continuous_mul [CommMonoid A] [τA : TopologicalSpace A] [ContinuousMul A]
    [CommMonoid B] (h : B →* A) :
    @ContinuousMul B (TopologicalSpace.induced h τA) _ := by
  convert (IsInducing.induced h).continuousMul h

end induced
