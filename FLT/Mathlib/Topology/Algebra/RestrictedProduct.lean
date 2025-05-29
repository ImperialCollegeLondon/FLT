import Mathlib.Topology.Algebra.RestrictedProduct
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib

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

-- def mulSingle [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] [DecidableEq ι] (j : ι) (x : R j) :
--     Πʳ i, [R i, B i] :=
--   ⟨Pi.mulSingle j x, sorry⟩ -- {i} is finite

-- def mulSingleMonoidHom [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] [DecidableEq ι]
--     (j : ι) : R j →* Πʳ i, [R i, B i] where
--       toFun := mulSingle j
--       map_one' := sorry -- should be easy
--       map_mul' := sorry -- should be easy

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
  exact (RestrictedProduct.continuous_inclusion hT).comp hc

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
        toFun u := ⟨fun i ↦ ⟨u.1 i, u⁻¹.1 i, congr($u.mul_inv i), congr($u.inv_mul i)⟩,
          by filter_upwards [u.val.2, u⁻¹.val.2] using fun i hi hi' ↦ ⟨hi, hi'⟩⟩
        invFun ui := ⟨⟨fun i ↦ ui i, by filter_upwards [ui.2] using fun i hi ↦ hi.1⟩,
          ⟨fun i ↦ ui⁻¹ i, by filter_upwards [ui⁻¹.2] using fun i hi ↦ hi.1⟩,
          by ext i; exact (ui i).mul_inv,
          by ext i; exact (ui i).inv_mul⟩
        left_inv u := by ext; rfl
        right_inv ui := by ext; rfl
        map_mul' u v := by ext; rfl

def Equiv.restrictedProductProd {ι : Type*} {ℱ : Filter ι}
    {A B : ι → Type*}
    {C : (i : ι) → Set (A i)}
    {D : (i : ι) → Set (B i)} :
    Πʳ i, [A i × B i, C i ×ˢ D i]_[ℱ] ≃ (Πʳ i, [A i, C i]_[ℱ]) × (Πʳ i, [B i, D i]_[ℱ]) where
      toFun x := (⟨fun i ↦ (x i).1, by filter_upwards [x.2] with i; exact And.left⟩,
                  ⟨fun i ↦ (x i).2, by filter_upwards [x.2] with i; exact And.right⟩)
      invFun yz := ⟨fun i ↦ (yz.1 i, yz.2 i), by
        filter_upwards [yz.1.2, yz.2.2] with i
        exact Set.mk_mem_prod⟩
      left_inv x := by ext <;> rfl
      right_inv y := by ext <;> rfl

def Homeomorph.restrictedProductProd {ι : Type*}
    {A B : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    {C : (i : ι) → Set (A i)} (hCopen : ∀ (i : ι), IsOpen (C i))
    {D : (i : ι) → Set (B i)} (hCopen : ∀ (i : ι), IsOpen (D i)) :
    Πʳ i, [A i × B i, C i ×ˢ D i] ≃ₜ (Πʳ i, [A i, C i]) × (Πʳ i, [B i, D i]) where
      __ := Equiv.restrictedProductProd
      continuous_toFun := sorry -- FLT#568
      continuous_invFun := sorry -- FLT#568

-- Is there a mathlibism for {f | ∀ j, f j ∈ C j i}?
def Equiv.restrictedProductPi {ι : Type*} {ℱ : Filter ι} {n : Type*} [Fintype n]
    {A : n → ι → Type*}
    {C : (j : n) → (i : ι) → Set (A j i)} :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}]_[ℱ] ≃ Π j, Πʳ i, [A j i, C j i]_[ℱ] where
      toFun x j := ⟨fun i ↦ x i j, by filter_upwards [x.2] with i h; exact h j⟩
      invFun y := ⟨fun i j ↦ y j i, by sorry⟩ -- FLT#569
      left_inv x := by ext; rfl
      right_inv y := by ext; rfl

def Homeomorph.restrictedProductPi {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)]
    {C : (j : n) → (i : ι) → Set (A j i)} (hCopen : ∀ j i, IsOpen (C j i)) :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}] ≃ₜ Π j, (Πʳ i, [A j i, C j i]) where
      __ := Equiv.restrictedProductPi
      continuous_toFun := sorry -- #570
      continuous_invFun := sorry -- #570

def Equiv.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*}
    {C : (i : ι) → Set (A i)} :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ Matrix m n (Πʳ i, [A i, C i])  where
      toFun x a b := ⟨fun i ↦ x i a b, by filter_upwards [x.2] with i h; exact h a b⟩
      invFun y := ⟨fun i a b ↦ y a b i, by sorry⟩ -- FLT#569
      left_inv x := by ext; rfl
      right_inv y := by ext; rfl

def Homeomorph.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    {C : (i : ι) → Set (A i)} (hCopen : ∀ i, IsOpen (C i)) :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ₜ Matrix m n (Πʳ i, [A i, C i])  where
      __ := Equiv.restrictedProductMatrix
      continuous_toFun := sorry  --#571
      continuous_invFun := sorry --#571
