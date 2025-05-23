import Mathlib.Topology.Algebra.RestrictedProduct
import Mathlib.Topology.Algebra.ContinuousMonoidHom

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
@[nolint unusedArguments] -- this can be removed when the FLT#530 proof is done
def congrRight (φ : (i : ι) → G i → H i)
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[ℱ]) : (Πʳ i, [H i, D i]_[ℱ]) :=
  ⟨fun i ↦ φ i (x i), sorry⟩ -- FLT#530

end RestrictedProduct

open RestrictedProduct

-- Now let's add continuity.

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)] in
theorem Continuous.restrictedProduct_congrRight {φ : (i : ι) → G i → H i}
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (C i) (D i))
    (hφcont : ∀ i, Continuous (φ i)) :
    Continuous (RestrictedProduct.congrRight φ hφ) := by
  sorry -- FLT#531 (feel free to add any of : ℱ is cofinite, Cᵢ are open/compact,
  -- but only add if necessary. I don't immediately see that we need them)

-- now let's add groups

variable {S T : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

variable [Π i, Monoid (G i)] [Π i, SubmonoidClass (S i) (G i)]
    [Π i, Monoid (H i)] [Π i, SubmonoidClass (T i) (H i)] in
/-- The maps between restricted products over a fixed index type,
given maps on the factors. -/
@[to_additive] -- this can be removed when the FLT#530 proof is done
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
@[to_additive (attr := simps!)]
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
@[to_additive]
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

#exit
/-
variable {S T : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

variable [Π i, Monoid (G i)] [Π i, SubmonoidClass (S i) (G i)]
    [Π i, Monoid (H i)] [Π i, SubmonoidClass (T i) (H i)] in
-/
def MulEquiv.restrictedProductUnits {ι : Type*} {ℱ : Filter ι}
    {M : ι → Type*} [(i : ι) → Monoid (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)]
    {A : Π i, S i} :
    (Πʳ i, [M i, A i])ˣ ≃* Πʳ i, [(M i)ˣ, {x : (M i)ˣ | x.1 ∈ A i}] := by
  sorry
