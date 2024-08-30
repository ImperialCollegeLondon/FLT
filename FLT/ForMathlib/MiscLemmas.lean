import Mathlib.Algebra.Module.Projective
import Mathlib.Topology.Algebra.Monoid

section elsewhere

variable {A : Type*} [AddCommGroup A]
variable {B : Type*} [AddCommGroup B]

lemma AddMonoidHom.sub_mem_ker_iff {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (φ : A →+ B) {x y : A} :
    x - y ∈ AddMonoidHom.ker φ ↔ φ x = φ y := by
  rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]

variable [τA : TopologicalSpace A] [ContinuousAdd A]
variable [τB : TopologicalSpace B]

lemma isOpenMap_of_coinduced (φ : A →+ B) (hφc : Continuous φ)
    (h : TopologicalSpace.coinduced φ τA = τB) :
    IsOpenMap φ := by
  intro U hU
  rw [← h, isOpen_coinduced]
  suffices ⇑φ ⁻¹' (⇑φ '' U) = ⋃ k ∈ φ.ker, (fun x ↦ x + k) ⁻¹' U by
    exact this ▸ isOpen_biUnion (fun k _ ↦ Continuous.isOpen_preimage (by continuity) _ hU)
  ext x
  constructor
  · rintro ⟨y, hyU, hyx⟩
    apply Set.mem_iUnion_of_mem (y - x)
    suffices y - x ∈ AddMonoidHom.ker φ by simp_all
    rwa [AddMonoidHom.sub_mem_ker_iff]
  · rintro ⟨_, ⟨k, rfl⟩, _, ⟨hk, rfl⟩, hx⟩
    use x + k, hx
    rw [AddMonoidHom.map_add, hk, add_zero]

-- **TODO** ask Yury how to golf
open TopologicalSpace in
lemma coinduced_prod_eq_prod_coinduced {X Y S T : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup S] [AddCommGroup T] (f : X →+ S) (g : Y →+ T)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [τX : TopologicalSpace X] [ContinuousAdd X] [τY : TopologicalSpace Y] [ContinuousAdd Y] :
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
      @isOpenMap_of_coinduced _ _ _ _ _ _ (coinduced f τX) f
        (by rw [continuous_iff_coinduced_le]) rfl V1 hV1,
      @isOpenMap_of_coinduced _ _ _ _ _ _ (coinduced g τY) g
        (by rw [continuous_iff_coinduced_le]) rfl V2 hV2,
      ⟨x, hx1, rfl⟩, ⟨y, hy2, rfl⟩
    rintro ⟨s, t⟩ ⟨⟨x', hx', rfl⟩, ⟨y', hy', rfl⟩⟩
    exact @h12 (x', y') ⟨hx', hy'⟩
  · intro h x y hxy
    rw [Set.mem_preimage, Prod.map_apply] at hxy
    obtain ⟨U1, U2, hU1, hU2, hx1, hy2, h12⟩ := h (f x) (g y) hxy
    use f ⁻¹' U1, g ⁻¹' U2, hU1, hU2, hx1, hy2
    intro ⟨x', y'⟩ ⟨hx', hy'⟩
    exact h12 ⟨hx', hy'⟩

end elsewhere

section missing_API

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P]

namespace Module

-- all done for rings bu it should be semirings

/-- Free modules are projective. -/
theorem Projective.of_basis' {ι : Type*} (b : Basis ι R P) : Projective R P := by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr ℕ fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.total_single,
    map_finsupp_sum]
  exact b.total_repr m

instance (priority := 100) Projective.of_free' [Module.Free R P] : Module.Projective R P :=
  .of_basis' <| Module.Free.chooseBasis R P

end Module

end missing_API

theorem TopologicalSpace.prod_mono {α β : Type*} {σ₁ σ₂ : TopologicalSpace α}
    {τ₁ τ₂ : TopologicalSpace β} (hσ : σ₁ ≤ σ₂) (hτ : τ₁ ≤ τ₂) :
    @instTopologicalSpaceProd α β σ₁ τ₁ ≤ @instTopologicalSpaceProd α β σ₂ τ₂ :=
  le_inf (le_trans inf_le_left <| induced_mono hσ)
         (le_trans inf_le_right <| induced_mono hτ)

section continuous_smul

variable {R : Type*} [τR : TopologicalSpace R]
variable {A : Type*} [SMul R A]
variable {S : Type*} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)
variable {B : Type*} [SMul S B]

-- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B
lemma induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] (g : B →ₑ[f] A) :
    @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
  convert Inducing.continuousSMul (inducing_induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

lemma induced_continuous_add [AddCommMonoid A] [τA : TopologicalSpace A] [ContinuousAdd A]
    [AddCommMonoid B] (h : B →+ A) :
    @ContinuousAdd B (TopologicalSpace.induced h τA) _ := by
  convert Inducing.continuousAdd h (inducing_induced h)

-- this should be elsewhere
lemma TopologicalSpace.induced_id (X : Type*) : TopologicalSpace.induced (id : X → X) = id := by
  ext τ S
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact hT
  · rintro hS
    exact ⟨S, hS, rfl⟩

-- #check Prod.continuousSMul -- exists and is an instance :-)
--#check Induced.continuousSMul -- doesn't exist

end continuous_smul
