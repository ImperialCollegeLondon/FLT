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

-- the below is all done for rings but it should be semirings
/-- Free modules are projective. -/
theorem Projective.of_basis' {ι : Type*} (b : Basis ι R P) : Projective R P := by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr ℕ fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.linearCombination_single,
    map_finsupp_sum]
  exact b.linearCombination_repr m

instance (priority := 100) Projective.of_free' [Module.Free R P] : Module.Projective R P :=
  .of_basis' <| Module.Free.chooseBasis R P

end Module

end missing_API

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
lemma induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] (g : B →ₑ[f] A)
    (hf : Continuous f) : @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
  convert Inducing.continuousSMul (inducing_induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

lemma induced_continuous_add [AddCommMonoid A] [τA : TopologicalSpace A] [ContinuousAdd A]
    [AddCommMonoid B] (h : B →+ A) :
    @ContinuousAdd B (TopologicalSpace.induced h τA) _ := by
  convert Inducing.continuousAdd h (inducing_induced h)

lemma induced_sInf {α β : Type*} {g : β → α}
    {s : Set (TopologicalSpace α)} :
    TopologicalSpace.induced g (sInf s) =
    sInf ((TopologicalSpace.induced g) '' s) := by
  rw [sInf_eq_iInf' s, sInf_image']
  exact induced_iInf

end induced

-- elsewhere
theorem _root_.Homeomorph.coinducing {A B : Type*} [τA : TopologicalSpace A]
    [τB : TopologicalSpace B] (e : A ≃ₜ B) : τB = τA.coinduced e := by
  ext U
  nth_rw 2 [isOpen_coinduced]
  exact e.isOpen_preimage.symm

-- elsewhere
lemma Homeomorph.symm_apply_eq {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] (e : M ≃ₜ N) {x : N} {y : M} :
  e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _

lemma finsum_option {ι : Type*} {B : Type*} [Finite ι]
    [AddCommMonoid B] (φ : Option ι → B) :
    (∑ᶠ oi, φ oi) = φ none + ∑ᶠ (j : ι),  φ (some j) := by
  rw [← finsum_mem_univ]
  convert finsum_mem_insert φ (show none ∉ Set.range Option.some by aesop)
    (Set.finite_range some)
  · aesop
  · rw [finsum_mem_range]
    exact Option.some_injective ι

lemma LinearMap.finsum_apply {R : Type*} [Semiring R] {A B : Type*} [AddCommMonoid A] [Module R A]
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
    [∀ st, AddCommGroup (A st)] [∀ st, Module R (A st)] :
    (∀ (st : S ⊕ T), A st) ≃ₗ[R] (∀ (s : S), A (.inl s)) × (∀ (t : T), A (.inr t)) where
      toFun f := (fun s ↦ f (.inl s), fun t ↦ f (.inr t))
      map_add' f g := by aesop
      map_smul' := by aesop
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
  left_inv x := by aesop
  right_inv x := by aesop
  continuous_toFun := by simp; fun_prop
  continuous_invFun := by simp; fun_prop

-- elsewhere
variable (R : Type*) [Semiring R] in
def LinearEquiv.pUnitPiEquiv (f : PUnit → Type*) [∀ x, AddCommGroup (f x)] [∀ x, Module R (f x)] :
    ((t : PUnit) → (f t)) ≃ₗ[R] f () where
  toFun a := a ()
  invFun a _t := a
  left_inv x := by aesop
  right_inv x := by aesop
  map_add' f g := rfl
  map_smul' r f := rfl

-- elsewhere
lemma finsum_apply {α ι N : Type*} [AddCommMonoid N] [Finite ι]
    (f : ι → α → N) (a : α) : (∑ᶠ i, f i) a = ∑ᶠ i, (f i) a := by
  classical
  simp only [finsum_def, dif_pos (Set.toFinite _), Finset.sum_apply]
  symm
  apply Finset.sum_subset <;> aesop
