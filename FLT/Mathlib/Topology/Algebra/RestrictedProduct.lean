import Mathlib.Topology.Algebra.RestrictedProduct
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Group.Submonoid.Units

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι → Type*} {A : (i : ι) → Set (R i)}
variable {ℱ : Filter ι}

/-- Constructor for `RestrictedProduct`. -/
abbrev mk (x : Π i, R i) (hx : ∀ᶠ i in ℱ, x i ∈ A i) : Πʳ i, [R i, A i]_[ℱ] :=
  ⟨x, hx⟩

@[simp]
lemma mk_apply (x : Π i, R i) (hx : ∀ᶠ i in ℱ, x i ∈ A i) (i : ι) :
    (mk x hx) i = x i := rfl

@[to_additive (attr := simp)]
lemma mul_apply {S : ι → Type*} [(i : ι) → SetLike (S i) (R i)] {B : (i : ι) → S i}
    [(i : ι) → Mul (R i)] [∀ (i : ι), MulMemClass (S i) (R i)]
    (x y : Πʳ (i : ι), [R i, ↑(B i)]_[ℱ]) (i : ι) : (x * y) i = x i * y i := rfl

variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}
variable {ℱ : Filter ι}

@[simp]
lemma one_apply [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] {i : ι} :
  (1 : Πʳ i, [R i, B i]_[ℱ]) i = 1 := rfl

variable
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

/-- The maps between restricted products over a fixed index type,
given maps on the factors. -/
def congrRight (φ : (i : ι) → G i → H i)
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[ℱ]) : (Πʳ i, [H i, D i]_[ℱ]) :=
  map G H id Filter.tendsto_id φ hφ x

end RestrictedProduct

open RestrictedProduct

-- Now let's add continuity.

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

variable {ι₂ : Type*} {𝒢 : Filter ι₂} {G₂ : ι₂ → Type*}
    {C₂ : (i : ι₂) → Set (G₂ i)} {f : ι₂ → ι} (hf : Filter.Tendsto f 𝒢 ℱ)
    [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (G₂ i)] in
theorem Continuous.restrictedProduct_map {φ : (j : ι₂) → G (f j) → G₂ j}
    (hφ : ∀ᶠ j in 𝒢, Set.MapsTo (φ j) (C (f j)) (C₂ j))
    (hφcont : ∀ i, Continuous (φ i)) :
    Continuous (map G G₂ f hf φ hφ) := by
  rw [continuous_dom]
  intro S hS
  rw [Filter.le_principal_iff] at hS
  set T := {x | Set.MapsTo (φ x) (C (f x)) (C₂ x)}
  have hT : 𝒢 ≤ Filter.principal ((f ⁻¹' S) ∩ T) := by
    rw [Filter.le_principal_iff]
    apply Filter.inter_mem _ hφ
    exact hf hS
  have hST : Filter.Tendsto f (Filter.principal ((f ⁻¹' S) ∩ T)) (Filter.principal S) := by
    rw [Filter.tendsto_principal_principal]
    exact fun a ⟨ha, _⟩ ↦ ha
  have hφ' : ∀ᶠ (j : ι₂) in Filter.principal ((f ⁻¹' S) ∩ T), Set.MapsTo (φ j) (C (f j)) (C₂ j) :=
    Filter.mem_principal.mpr Set.inter_subset_right
  have hc : Continuous (map G G₂ f hST φ hφ') := by
    rw [continuous_rng_of_principal]
    apply continuous_pi
    intro i
    apply (hφcont i).comp <| (continuous_apply (f i)).comp continuous_coe
  exact (continuous_inclusion hT).comp hc

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)] in
theorem Continuous.restrictedProduct_congrRight {φ : (i : ι) → G i → H i}
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (C i) (D i))
    (hφcont : ∀ i, Continuous (φ i)) :
    Continuous (congrRight φ hφ) :=
  Continuous.restrictedProduct_map Filter.tendsto_id hφ hφcont

-- now let's add groups

variable {S T : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

variable [Π i, Monoid (G i)] [Π i, SubmonoidClass (S i) (G i)]
    [Π i, Monoid (H i)] [Π i, SubmonoidClass (T i) (H i)] in
/-- The monoid homomorphism between restricted products over a fixed index type,
given monoid homomorphisms on the factors. -/
@[to_additive "The additive monoid homomorphism between restricted products over a fixed index type,
given additive monoid homomorphisms on the factors."]
def MonoidHom.restrictedProductCongrRight (φ : (i : ι) → G i →* H i)
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (A i) (B i)) :
    Πʳ i, [G i, A i]_[ℱ] →* Πʳ i, [H i, B i]_[ℱ] where
      toFun := congrRight (fun i ↦ φ i) hφ
      map_one' := by ext; simp [congrRight]
      map_mul' x y := by ext; simp [congrRight]

variable [Π i, Monoid (G i)] [Π i, SubmonoidClass (S i) (G i)]
    [Π i, Monoid (H i)] [Π i, SubmonoidClass (T i) (H i)]
    [Π i, TopologicalSpace (G i)]
    [Π i, TopologicalSpace (H i)] in
/-- The continuous monoid homomorphism between restricted products built from
continuous monoid homomorphisms on the factors. -/
@[to_additive (attr := simps!) "The continuous additive monoid homomorphism between restricted
products, built from continuous monoid homomorphisms on the factors."]
def ContinuousMonoidHom.restrictedProductCongrRight (φ : (i : ι) → G i →ₜ* H i)
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (A i) (B i)) :
    Πʳ i, [G i, A i]_[ℱ] →ₜ* Πʳ i, [H i, B i]_[ℱ] where
  __ := MonoidHom.restrictedProductCongrRight (fun i ↦ φ i) hφ
  continuous_toFun := by exact
    Continuous.restrictedProduct_congrRight (φ := fun i ↦ φ i) hφ (fun i ↦ (φ i).continuous)

variable [Π i, Monoid (G i)] [Π i, SubmonoidClass (S i) (G i)]
    [Π i, Monoid (H i)] [Π i, SubmonoidClass (T i) (H i)]
    [Π i, TopologicalSpace (G i)]
    [Π i, TopologicalSpace (H i)] in
/-- The `ContinuousMulEquiv` (that is, group isomorphism and homeomorphism) between restricted
products built from `ContinuousMulEquiv`s on the factors. -/
@[to_additive "The `ContinuousAddEquiv` (that is, additive group isomorphism and homeomorphism)
between restricted products built from `ContinuousAddEquiv`s on the factors."]
def ContinuousMulEquiv.restrictedProductCongrRight (φ : (i : ι) → G i ≃ₜ* H i)
    (hφ : ∀ᶠ i in ℱ, Set.BijOn (φ i) (A i) (B i)) :
    (Πʳ i, [G i, A i]_[ℱ]) ≃ₜ* (Πʳ i, [H i, B i]_[ℱ]) where
  __ := ContinuousMonoidHom.restrictedProductCongrRight (fun i ↦ φ i)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo)
  invFun := ContinuousMonoidHom.restrictedProductCongrRight (fun i ↦ (φ i).symm)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm)
  left_inv x := by
    ext i
    exact ContinuousMulEquiv.symm_apply_apply _ _
  right_inv x := by
    ext i
    exact ContinuousMulEquiv.apply_symm_apply _ _

/-- The isomorphism between the units of a restricted product of monoids,
and the restricted product of the units of the monoids. -/
def MulEquiv.restrictedProductUnits {ι : Type*} {ℱ : Filter ι}
    {M : ι → Type*} [(i : ι) → Monoid (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)]
    (A : Π i, S i) :
    (Πʳ i, [M i, A i]_[ℱ])ˣ ≃*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units]_[ℱ] where
        toFun u := ⟨fun i ↦ ⟨u.1 i, u⁻¹.1 i, sorry, sorry⟩, sorry⟩
        invFun ui := ⟨⟨fun i ↦ ui i, sorry⟩, ⟨fun i ↦ ui⁻¹ i, sorry⟩, sorry, sorry⟩
        left_inv := sorry
        right_inv := sorry
        map_mul' := sorry -- all of these are FLT#553

theorem continuous_eval {ι : Type*} {ℱ : Filter ι}
    {R : ι → Type*} {A : Π i, Set (R i)} [∀ i, TopologicalSpace (R i)]
    (i : ι) : Continuous (fun (x : Πʳ i, [R i, A i]_[ℱ]) ↦ x i) :=
  continuous_apply _ |>.comp continuous_coe

-- TODO: find a better name ?
open Classical Filter in
noncomputable def Homeomorph.restrictedProductPrincipal {ι : Type*}
    (R : ι → Type*) (A : Π i, Set (R i)) [∀ i, TopologicalSpace (R i)] (J : Set ι) :
    Πʳ i, [R i, A i]_[𝓟 J] ≃ₜ (Π i : (Jᶜ : Set ι), R i) × (Π i : J, A i) where
  toFun x := ⟨fun i ↦ x i, fun i ↦ ⟨x i, eventually_principal.mp x.2 i i.2⟩⟩
  invFun x := ⟨fun i ↦ if h : i ∈ J then x.2 ⟨i, h⟩ else x.1 ⟨i, h⟩, by aesop⟩
  left_inv x := by ext; simp
  right_inv x := by
    ext i
    · simp [dif_neg i.2]
    · simp
  continuous_toFun := continuous_prodMk.mpr
    ⟨continuous_pi fun _ ↦ continuous_eval _,
      continuous_pi fun _ ↦ continuous_induced_rng.mpr <| continuous_eval _⟩
  continuous_invFun := by
    refine continuous_rng_of_principal.mpr <| continuous_pi fun i ↦ ?_
    by_cases hi : i ∈ J
    · simp only [Function.comp_apply, mk_apply, hi, ↓reduceDIte]
      fun_prop
    · simp only [Function.comp_apply, mk_apply, hi, ↓reduceDIte]
      fun_prop

open Filter in
noncomputable def ContinuousMulEquiv.restrictedProductPrincipal {ι : Type*}
    {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)] {A : Π i, S i}
    (J : Set ι) :
    Πʳ i, [R i, A i]_[𝓟 J] ≃ₜ* (Π i : (Jᶜ : Set ι), R i) × (Π i : J, A i) where
  toHomeomorph := Homeomorph.restrictedProductPrincipal R (fun i ↦ A i) J
  map_mul' _ _ := rfl
