import Mathlib.Algebra.Module.Projective
import Mathlib.Topology.Algebra.Monoid
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib
section elsewhere

variable {A : Type*} [AddCommGroup A]
variable {B : Type*} [AddCommGroup B]
variable [τA : TopologicalSpace A] [ContinuousAdd A]
variable [τB : TopologicalSpace B]

theorem isOpenMap_of_coinduced (φ : A →+ B) (hφc : Continuous φ)
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
theorem coinduced_prod_eq_prod_coinduced {X Y S T : Type*} [AddCommGroup X] [AddCommGroup Y]
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
    exact ⟨f ⁻¹' U1, g ⁻¹' U2, hU1, hU2, hx1, hy2, fun ⟨x', y'⟩ ⟨hx', hy'⟩ ↦ h12 ⟨hx', hy'⟩⟩

end elsewhere

theorem TopologicalSpace.prod_mono {α β : Type*} {σ₁ σ₂ : TopologicalSpace α}
    {τ₁ τ₂ : TopologicalSpace β} (hσ : σ₁ ≤ σ₂) (hτ : τ₁ ≤ τ₂) :
    @instTopologicalSpaceProd α β σ₁ τ₁ ≤ @instTopologicalSpaceProd α β σ₂ τ₂ :=
  le_inf (le_trans inf_le_left <| induced_mono hσ)
         (le_trans inf_le_right <| induced_mono hτ)

section induced

variable {R : Type*} [τR : TopologicalSpace R]
variable {A : Type*} [SMul R A]
variable {S : Type*} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)
variable {B : Type*} [SMul S B]

-- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B
theorem induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] (g : B →ₑ[f] A)
    (hf : Continuous f) : @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
  convert IsInducing.continuousSMul (IsInducing.induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

theorem induced_continuous_add [AddCommMonoid A] [τA : TopologicalSpace A] [ContinuousAdd A]
    [AddCommMonoid B] (h : B →+ A) :
    @ContinuousAdd B (TopologicalSpace.induced h τA) _ := by
  convert IsInducing.continuousAdd h (IsInducing.induced h)

end induced

-- elsewhere
theorem _root_.Homeomorph.coinducing {A B : Type*} [τA : TopologicalSpace A]
    [τB : TopologicalSpace B] (e : A ≃ₜ B) : τB = τA.coinduced e := by
  ext U
  nth_rw 2 [isOpen_coinduced]
  exact e.isOpen_preimage.symm

-- elsewhere
theorem Homeomorph.symm_apply_eq {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] (e : M ≃ₜ N) {x : N} {y : M} :
  e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _

theorem finsum_option {ι : Type*} {B : Type*} [Finite ι]
    [AddCommMonoid B] (φ : Option ι → B) :
    (∑ᶠ oi, φ oi) = φ none + ∑ᶠ (j : ι),  φ (some j) := by
  rw [← finsum_mem_univ]
  convert finsum_mem_insert φ (show none ∉ Set.range Option.some by aesop)
    (Set.finite_range some)
  · exact (Set.insert_none_range_some ι).symm
  · rw [finsum_mem_range]
    exact Option.some_injective ι

theorem LinearMap.finsum_apply {R : Type*} [Semiring R] {A B : Type*} [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] {ι : Type*} [Finite ι] (φ : ∀ _ : ι, A →ₗ[R] B) (a : A) :
    (∑ᶠ i, φ i) a = ∑ᶠ i, φ i a := by
  induction ι using Finite.induction_empty_option
  · case of_equiv X Y e hx =>
    convert hx (φ ∘ e)
    · exact (finsum_comp_equiv e).symm
    · exact (finsum_comp_equiv e).symm
  · simp [finsum_of_isEmpty]
  · case h_option X _ hX =>
    simp [finsum_option, hX]

-- more continuous linear equiv stuff
-- elsewhere
variable (R : Type*) [Semiring R] in
def LinearEquiv.sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)] :
    (∀ (st : S ⊕ T), A st) ≃ₗ[R] (∀ (s : S), A (.inl s)) × (∀ (t : T), A (.inr t)) where
      toFun f := (fun s ↦ f (.inl s), fun t ↦ f (.inr t))
      map_add' f g := rfl
      map_smul' _ _ := rfl
      invFun fg st := Sum.rec (fun s => fg.1 s) (fun t => fg.2 t) st
      left_inv := by intro x; aesop
      right_inv := by intro x; aesop

-- elsewhere
def Homeomorph.sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, TopologicalSpace (A st)] :
    (∀ (st : S ⊕ T), A st) ≃ₜ (∀ (s : S), A (.inl s)) × (∀ (t : T), A (.inr t)) where
      toFun f := (fun s ↦ f (.inl s), fun t ↦ f (.inr t))
      invFun fg st := Sum.rec (fun s => fg.1 s) (fun t => fg.2 t) st
      left_inv := by intro x; aesop
      right_inv := by intro x; aesop
      continuous_toFun := Continuous.prod_mk (by fun_prop) (by fun_prop)
      continuous_invFun := continuous_pi <| fun st ↦ by
        rcases st with s | t
        · simp
          fun_prop
        · simp
          fun_prop

-- elsewhere
def Homeomorph.pUnitPiEquiv (f : PUnit → Type*) [∀ x, TopologicalSpace (f x)]: ((t : PUnit) → (f t)) ≃ₜ f () where
  toFun a := a ()
  invFun a _t := a
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by simp; fun_prop
  continuous_invFun := by simp; fun_prop

-- elsewhere
variable (R : Type*) [Semiring R] in
def LinearEquiv.pUnitPiEquiv (f : PUnit → Type*) [∀ x, AddCommMonoid (f x)] [∀ x, Module R (f x)] :
    ((t : PUnit) → (f t)) ≃ₗ[R] f () where
  toFun a := a ()
  invFun a _t := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- elsewhere
theorem finsum_apply {α ι N : Type*} [AddCommMonoid N] [Finite ι]
    (f : ι → α → N) (a : α) : (∑ᶠ i, f i) a = ∑ᶠ i, (f i) a := by
  classical
  simp only [finsum_def, dif_pos (Set.toFinite _), Finset.sum_apply]
  symm
  apply Finset.sum_subset <;> aesop
