import Mathlib.Topology.Algebra.RestrictedProduct
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.Matrix
import FLT.Mathlib.Topology.Algebra.Group.Units


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

variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}
variable {ℱ : Filter ι}

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

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)] in
@[fun_prop]
theorem Continuous.restrictedProduct_congrRight {φ : (i : ι) → G i → H i}
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (C i) (D i))
    (hφcont : ∀ i, Continuous (φ i)) :
    Continuous (congrRight φ hφ) :=
  map_continuous G H id Filter.tendsto_id φ hφ hφcont

-- now let's add groups

section groups

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
    {A : Π i, S i} :
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

end groups

section binary

variable {ι : Type*} {ℱ : Filter ι} {A B : ι → Type*}
  {C : (i : ι) → Set (A i)} {D : (i : ι) → Set (B i)}


/-- The bijection between a restricted product of binary products, and the binary product
of the restricted products. -/
@[simps]
def Equiv.restrictedProductProd :
    Πʳ i, [A i × B i, C i ×ˢ D i]_[ℱ] ≃ (Πʳ i, [A i, C i]_[ℱ]) × (Πʳ i, [B i, D i]_[ℱ]) where
  toFun x := (congrRight (fun i (t : A i × B i) ↦ t.1) (by simp +contextual [Set.MapsTo]) x,
              congrRight (fun i (t : A i × B i) ↦ t.2) (by simp +contextual [Set.MapsTo]) x)
  invFun yz :=
    ⟨fun i ↦ (yz.1 i, yz.2 i), by
    filter_upwards [yz.1.2, yz.2.2] with i using Set.mk_mem_prod⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl

lemma Equiv.restrictedProductProd_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductProd.symm ∘ Prod.map (inclusion _ _ hℱ) (inclusion _ _ hℱ) =
      inclusion (fun i ↦ A i × B i) (fun i ↦ C i ×ˢ D i) hℱ ∘ Equiv.restrictedProductProd.symm :=
  rfl

/--
The forward direction of `Equiv.restrictedProductProd` is continuous with any filter, not just the
cofinite one
-/
lemma Equiv.continuous_restrictedProductProd
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Continuous (Equiv.restrictedProductProd (C := C) (D := D) (ℱ := ℱ)) := by
  simp only [Equiv.restrictedProductProd, coe_fn_mk]
  fun_prop

lemma continuous_rng_of_principal_pi
    [(i : ι) → TopologicalSpace (A i)] {S : Set ι} {X : Type*} [TopologicalSpace X]
    {f : X → Πʳ (i : ι), [A i, C i]_[Filter.principal S]} :
    Continuous f ↔ ∀ i : ι, Continuous ((fun x ↦ x i) ∘ f) := by
  rw [continuous_rng_of_principal, continuous_pi_iff]
  rfl

@[fun_prop]
lemma Equiv.continuous_restrictedProductProd_symm {S : Set ι}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Continuous (Equiv.restrictedProductProd (C := C) (D := D) (ℱ := .principal S)).symm := by
  simp only [restrictedProductProd, coe_fn_symm_mk]
  rw [continuous_rng_of_principal_pi]
  intro i
  rw [continuous_prodMk]
  constructor
  · exact (RestrictedProduct.continuous_eval i).comp continuous_fst
  · exact (RestrictedProduct.continuous_eval i).comp continuous_snd

/-- The homeomorphism between restricted product of binary products, and the binary projuct
of the restricted products, when the products are with respect to open subsets.
-/
def Homeomorph.restrictedProductProd [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    (hCopen : ∀ (i : ι), IsOpen (C i)) (hDopen : ∀ (i : ι), IsOpen (D i)) :
    Πʳ i, [A i × B i, C i ×ˢ D i] ≃ₜ (Πʳ i, [A i, C i]) × (Πʳ i, [B i, D i]) where
  __ := Equiv.restrictedProductProd
  continuous_toFun := Equiv.continuous_restrictedProductProd
  continuous_invFun := by
    rw [RestrictedProduct.continuous_dom_prod hCopen hDopen]
    intro S hS
    rw [Equiv.invFun_as_coe, Equiv.restrictedProductProd_symm_comp_inclusion]
    fun_prop

end binary

section pi

variable {ι : Type*} {ℱ : Filter ι} {n : Type*} [Fintype n]
    {A : n → ι → Type*}
    {C : (j : n) → (i : ι) → Set (A j i)}

-- Q: Is there a mathlibism for `{f | ∀ j, f j ∈ C j i}`?
-- A: Yes, `Set.pi Set.univ`, except that it's defeq to `{f | ∀ j ∈ univ, f j ∈ C j i}`

/-- The bijection between a restricted product of finite products, and a finite product
of restricted products.
-/
def Equiv.restrictedProductPi :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}]_[ℱ] ≃ Π j, Πʳ i, [A j i, C j i]_[ℱ] where
  toFun x j := congrRight (fun i t ↦ t _) (by simp +contextual [Set.MapsTo]) x
  invFun y := .mk (fun i j ↦ y j i) (by simp)
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

lemma Equiv.restrictedProductPi_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductPi.symm ∘ Pi.map (fun i ↦ inclusion (A i) (C i) hℱ) =
      inclusion _ _ hℱ ∘ Equiv.restrictedProductPi.symm :=
  rfl

open Filter

/--
The forward direction of `Equiv.restrictedProductPi` is continuous with any filter, not just the
cofinite one
-/
lemma Equiv.continuous_restrictedProductPi [∀ j i, TopologicalSpace (A j i)] :
    Continuous (Equiv.restrictedProductPi (C := C) (ℱ := ℱ)) := by
  simp only [Equiv.restrictedProductPi, coe_fn_mk]
  fun_prop

@[fun_prop]
lemma Equiv.continuous_restrictedProductPi_symm {S : Set ι}
    [∀ j i, TopologicalSpace (A j i)] :
    Continuous (Equiv.restrictedProductPi (C := C) (ℱ := .principal S)).symm := by
  simp only [restrictedProductProd, coe_fn_symm_mk]
  rw [continuous_rng_of_principal_pi]
  intro i
  rw [continuous_pi_iff]
  intro j
  exact (RestrictedProduct.continuous_eval i).comp (_root_.continuous_apply _)

/-- The homeomorphism between a restricted product of finite products, and a finite product
of restricted products, when the products are with respect to open subsets.
-/
def Homeomorph.restrictedProductPi {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)]
    {C : (j : n) → (i : ι) → Set (A j i)} (hCopen : ∀ j i, IsOpen (C j i)) :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}] ≃ₜ Π j, (Πʳ i, [A j i, C j i]) where
  __ := Equiv.restrictedProductPi
  continuous_toFun := Equiv.continuous_restrictedProductPi
  continuous_invFun := by
    rw [RestrictedProduct.continuous_dom_pi hCopen]
    intro S hS
    rw [Equiv.invFun_as_coe, Equiv.restrictedProductPi_symm_comp_inclusion]
    fun_prop

/-- The bijection between a restricted product of m x n matrices, and m x n matrices
of restricted products.
-/
def Equiv.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*}
    {C : (i : ι) → Set (A i)} :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ Matrix m n (Πʳ i, [A i, C i]) :=
  Equiv.restrictedProductPi.trans (Equiv.piCongrRight fun _ ↦ Equiv.restrictedProductPi)

theorem Homeomorph.restrictedProductMatrix_aux {ι n : Type*} [Fintype n] {A : ι → Type*}
    [(i : ι) → TopologicalSpace (A i)] {C : (i : ι) → Set (A i)}
    (i : ι) (hCopen : ∀ (i : ι), IsOpen (C i)) :
    IsOpen {f : n → A i | ∀ (a : n), f a ∈ C i} := by
  convert isOpen_set_pi (s := fun _ : n ↦ C i) (Set.toFinite .univ) (fun _ _ ↦ hCopen i)
  ext f
  simp

/-- The homeomorphism between a restricted product of m x n matrices, and m x n matrices
of restricted products, when the products are with respect to open sets.
-/
def Homeomorph.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    {C : (i : ι) → Set (A i)} (hCopen : ∀ i, IsOpen (C i)) :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ₜ Matrix m n (Πʳ i, [A i, C i]) :=
  (Homeomorph.restrictedProductPi (fun _ _ ↦ restrictedProductMatrix_aux _ hCopen)).trans
    (Homeomorph.piCongrRight fun _ ↦ Homeomorph.restrictedProductPi (fun _ ↦ hCopen))

lemma Homeomorph.restrictedProductMatrix_toEquiv {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    {C : (i : ι) → Set (A i)} (hCopen : ∀ i, IsOpen (C i)) :
    (restrictedProductMatrix hCopen).toEquiv =
      Equiv.restrictedProductMatrix (m := m) (n := n) :=
  rfl

/-- The monoid homeomorphism between the units of a restricted product of topological monoids
and the restricted product of the units of the monoids, when the products are with
respect to open submonoids.
-/
def ContinuousMulEquiv.restrictedProductUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)]
    [(i : ι) → ContinuousMul (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)]
    (A : Π i, S i) (hA : ∀ i, IsOpen (A i : Set (M i))):
    (Πʳ i, [M i, A i])ˣ ≃ₜ*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units] :=
    have : Fact (∀ i, IsOpen (A i : Set (M i))) := Fact.mk hA
    have : Fact (∀ i, IsOpen ((Submonoid.ofClass (A i)).units : Set (M i)ˣ)) := Fact.mk <|
      fun i ↦ Submonoid.units_isOpen (hA i)
  {
  __ := MulEquiv.restrictedProductUnits
  continuous_toFun := by
    suffices ContinuousAt (MulEquiv.restrictedProductUnits : (Πʳ i, [M i, A i])ˣ ≃*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units]).toMonoidHom 1 from
      continuous_of_continuousAt_one MulEquiv.restrictedProductUnits this
    sorry -- #582
  continuous_invFun := by
    suffices ContinuousAt (MulEquiv.restrictedProductUnits : (Πʳ i, [M i, A i])ˣ ≃*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units]).symm.toMonoidHom 1 from
      continuous_of_continuousAt_one MulEquiv.restrictedProductUnits.symm this
    sorry -- #582
      }

end pi

section supports

namespace RestrictedProduct

variable {S T : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

-- this should all be for dependent functions

variable [(i : ι) → One (G i)] in
/-- The support of an element of a restricted product of monoids (or more generally,
objects with a 1. The support is the components which aren't 1.)
-/
@[to_additive "The support of an element of a restricted product of additive monoids
(or more generally, objects with a 0. The support is the components which aren't 0."]
def mulSupport (u : Πʳ i, [G i, A i]) : Set ι :=
  {i : ι | u i ≠ 1}

variable [(i : ι) → One (G i)] in
@[to_additive (attr := simp)]
lemma not_mem_mulSupport {u : Πʳ i, [G i, A i]} (i : ι) :
  i ∉ mulSupport u ↔ u i = 1 := by simp [mulSupport]

variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)] in
@[to_additive]
lemma mul_comm_of_disjoint_mulSupport {u v : Πʳ i, [G i, A i]}
    (h : mulSupport u ∩ mulSupport v = ∅) : u * v = v * u := by
  ext i
  obtain hi | hi : i ∉ u.mulSupport ∨ i ∉ v.mulSupport := by
    rw [Set.ext_iff] at h
    specialize h i
    tauto
  · rw [not_mem_mulSupport] at hi
    simp [hi]
  · rw [not_mem_mulSupport] at hi
    simp [hi]

variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)] in
@[to_additive]
lemma mulSupport_mul_subset {u v : Πʳ i, [G i, A i]} {J : Set ι} (hu : mulSupport u ⊆ J)
    (hv : mulSupport v ⊆ J) : mulSupport (u * v) ⊆ J := by
  intro i hi
  contrapose! hi
  simp [not_mem_mulSupport, (not_mem_mulSupport i).1 (fun a ↦ hi (hu a)),
    (not_mem_mulSupport i).1 (fun a ↦ hi (hv a))]

variable [(i : ι) → Group (G i)] [∀ i, SubgroupClass (S i) (G i)] in
@[to_additive (attr := simp)]
lemma mulSupport_inv {u : Πʳ i, [G i, A i]} : mulSupport u⁻¹ = mulSupport u := by
  ext i
  simp only [mulSupport]
  exact inv_ne_one

variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)]
    {T : Type*} [SetLike T (Πʳ i, [G i, A i])]
    [SubmonoidClass T (Πʳ i, [G i, A i])] in
/-- A submonoid `U` of a resticted product of monoids is a product at `i` if
`U` can be written as Uᵢ × Uⁱ with Uᵢ supported at the i'th component and Uⁱ supported
away from `i`.
-/
def SubmonoidClass.isProductAt (U : T) (i : ι) : Prop :=
  ∀ u ∈ U, ∃ uᵢ, uᵢ ∈ U ∧ ∃ uᵢ', uᵢ' ∈ U ∧ u = uᵢ * uᵢ' ∧ mulSupport uᵢ ⊆ {i} ∧ i ∉ mulSupport uᵢ'

variable [(i : ι) → Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    {T : Type*} [SetLike T (Πʳ i, [G i, A i])]
    [SubgroupClass T (Πʳ i, [G i, A i])] in
open scoped Pointwise in
/--
If `U` is a product at `i` and `g` is supported at `i` then `UgU` can be written as
a disjoint union of cosets `gᵢU` with the `gᵢ` supported at `i`.
-/
lemma mem_coset_and_mulSupport_subset_of_isProductAt
    {U : T} (i : ι) (g : Πʳ i, [G i, A i])
    (hU : SubmonoidClass.isProductAt U i) (hg : mulSupport g ⊆ {i}) (γ :  Πʳ i, [G i, A i])
    (hγ : γ ∈ U * g • (U : Set (Πʳ i, [G i, A i]))) :
    ∃ δ, δ ∈ γ • (U : Set (Πʳ i, [G i, A i])) ∧ mulSupport δ ⊆ {i} := by
  obtain ⟨u, hu, _, ⟨v, hv, rfl⟩, rfl⟩ := hγ
  obtain ⟨uᵢ, huᵢU, uᵢ', huᵢ'U, rfl, huᵢ, huᵢ'⟩ := hU u hu
  refine ⟨uᵢ * g, ⟨v⁻¹ * uᵢ'⁻¹, mul_mem (inv_mem hv) (inv_mem huᵢ'U), by
    have hcomm : g * uᵢ'⁻¹ = uᵢ'⁻¹ * g := mul_comm_of_disjoint_mulSupport <| by
      rw [mulSupport_inv]
      -- X ⊆ {i}, i ∉ Y => X ∩ Y = ∅
      rw [Set.eq_empty_iff_forall_notMem]
      intro j ⟨hj1, hj2⟩
      apply huᵢ'
      apply hg at hj1
      simp_all
    simp only [smul_eq_mul, mul_assoc, mul_inv_cancel_left, mul_right_inj, hcomm]⟩,
    mulSupport_mul_subset huᵢ hg⟩

end RestrictedProduct

end supports

section flatten

namespace RestrictedProduct

variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)

variable (hf : Filter.Tendsto f ℱ 𝒢) in
/-- The canonical map from a restricted product of products over fibres of a map on indexing sets
to the restricted product over the original indexing set. -/
def flatten : Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] →
    Πʳ i, [G i, C i]_[ℱ] :=
  map _ G f hf (fun i x ↦ x ⟨i, rfl⟩) (by filter_upwards with x y hy using hy ⟨x, rfl⟩ trivial)

@[simp]
lemma flatten_apply (hf : Filter.Tendsto f ℱ 𝒢) (x) (i : ι) :
    flatten C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

variable (hf : Filter.comap f 𝒢 = ℱ)

/-- The canonical bijection from a restricted product of products over fibres of a map on indexing
sets to the restricted product over the original indexing set. -/
def flatten_equiv :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃
    Πʳ i, [G i, C i]_[ℱ] where
  toFun := flatten C (by rw [Filter.tendsto_iff_comap]; exact hf.ge)
  invFun := fun ⟨x, hx⟩ ↦ ⟨fun _ i ↦ x i, by
    rw [← hf, Filter.eventually_comap] at hx
    filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
  left_inv := by
    intro ⟨x, hx⟩
    ext _ ⟨i, rfl⟩
    rfl
  right_inv x := by ext i; rfl

@[simp]
lemma flatten_equiv_apply (x) (i : ι) :
    flatten_equiv C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_equiv C hf).symm x i j = x j.1 :=
  rfl

variable [Π i, TopologicalSpace (G i)]

/-- The canonical homeomorphism from a restricted product of products over fibres of a map on
indexing sets to the restricted product over the original indexing set. -/
def flatten_homeomorph :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃ₜ
    Πʳ i, [G i, C i]_[ℱ] where
  __ := flatten_equiv C hf
  continuous_toFun := by
    dsimp only [flatten_equiv, flatten]
    apply map_continuous
    fun_prop
  continuous_invFun := by
    dsimp only [flatten_equiv]
    rw [continuous_dom]
    intro S hS
    set T := (f '' Sᶜ)ᶜ with hTval
    have hT : 𝒢 ≤ Filter.principal T := by
      rwa [Filter.le_principal_iff, hTval, ← Filter.mem_comap_iff_compl, hf,
        ← Filter.le_principal_iff]
    let g : Πʳ i, [G i, C i]_[Filter.principal S] → Πʳ j, [Π (i : f ⁻¹' {j}), G i,
        Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[Filter.principal T] :=
      fun ⟨x, hx⟩ ↦ ⟨fun j i ↦ x i, by
        have : Filter.comap f (Filter.principal T) ≤ Filter.principal S := by
          rw [Filter.le_principal_iff, Filter.mem_comap]
          use T
          refine ⟨Filter.mem_principal_self T, ?_⟩
          rw [hTval, Set.preimage_compl, Set.compl_subset_comm]
          apply Set.subset_preimage_image
        have hx := Filter.Eventually.filter_mono this hx
        rw [Filter.eventually_comap] at hx
        filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
    let hc : Continuous g := by
      rw [continuous_rng_of_principal]
      apply continuous_pi
      intro j
      apply continuous_pi
      rintro ⟨i, rfl⟩
      exact continuous_eval i
    apply (continuous_inclusion hT).comp hc

@[simp]
lemma flatten_homeomorph_apply (x) (i : ι) :
    flatten_homeomorph C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_homeomorph_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_homeomorph C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

/-- The equivalence given by `flatten` when both restricted products are over the cofinite
filter. -/
def flatten_equiv' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃
    Πʳ i, [G i, C i] :=
  have hf : Filter.comap f Filter.cofinite = Filter.cofinite := by
    apply le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)
  flatten_equiv C hf

omit [(i : ι) → TopologicalSpace (G i)] in
@[simp]
lemma flatten_equiv'_apply (x) (i : ι) :
    flatten_equiv' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

omit [(i : ι) → TopologicalSpace (G i)] in
@[simp]
lemma flatten_equiv'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_equiv' C hf).symm x i j = x j.1 :=
  rfl

/-- The homeomorphism given by `flatten` when both restricted products are over the cofinite
filter and there's a topology on the factors. -/
def flatten_homeomorph' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃ₜ
    Πʳ i, [G i, C i] :=
  have hf : Filter.comap f Filter.cofinite = Filter.cofinite := by
    apply le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)
  flatten_homeomorph C hf

@[simp]
lemma flatten_homeomorph'_apply (x) (i : ι) :
    flatten_homeomorph' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_homeomorph'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_homeomorph' C hf).symm x i j = x j.1 :=
  rfl

end RestrictedProduct

end flatten

section single

namespace RestrictedProduct

variable {S : ι → Type*}
variable [Πi, SetLike (S i) (G i)]
variable (A : (i : ι) → (S i))
variable [DecidableEq ι]

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive "The function supported at `i`, with value `x` there, and `0` elsewhere."]
def mulSingle [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] (i : ι) (x : G i) :
    Πʳ i, [G i, A i] where
  val := Pi.mulSingle i x
  property := by
    rw [Filter.eventually_cofinite]
    apply Set.Subsingleton.finite
    apply Set.subsingleton_of_subset_singleton (a := i)
    apply Set.Subset.trans _ (Pi.mulSupport_mulSingle_subset (b := x))
    intro j hj
    rw [Function.mem_mulSupport]
    contrapose! hj
    rw [Set.mem_setOf, Set.not_notMem]
    convert one_mem (A j)
    by_cases hi : i = j
    · obtain rfl := hi
      exact hj
    · rw [Pi.mulSingle_eq_of_ne' hi]

@[to_additive]
lemma mulSingle_injective [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] (i : ι) :
    Function.Injective (mulSingle A i) := by
  intro a b h
  rw [Subtype.ext_iff] at h
  exact Pi.mulSingle_injective i h

@[to_additive]
lemma mulSingle_inj [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] (i : ι) {x y : G i} :
    mulSingle A i x = mulSingle A i y ↔ x = y := by
  rw [Subtype.ext_iff]
  exact Pi.mulSingle_inj i

@[to_additive (attr := simp)]
lemma mulSingle_eq_same [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] (i : ι) (r : G i) :
    mulSingle A i r i = r :=
  Pi.mulSingle_eq_same i r

@[to_additive (attr := simp)]
lemma mulSingle_eq_of_ne [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] {i j : ι} (r : G i)
    (h : j ≠ i) : mulSingle A i r j = 1 :=
  Pi.mulSingle_eq_of_ne h r

@[to_additive (attr := simp)]
lemma mulSingle_eq_of_ne' [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] {i j : ι} (r : G i)
    (h : i ≠ j) : mulSingle A i r j = 1 :=
  Pi.mulSingle_eq_of_ne' h r

@[to_additive (attr := simp)]
lemma mulSingle_one [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] (i : ι) :
    mulSingle A i 1 = 1 := by
  apply Subtype.ext
  exact Pi.mulSingle_one i

@[to_additive (attr := simp)]
lemma mulSingle_eq_one_iff [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] (i : ι) {x : G i} :
    mulSingle A i x = 1 ↔ x = 1 := by
  rw [Subtype.ext_iff]
  exact Pi.mulSingle_eq_one_iff

@[to_additive]
lemma mulSingle_ne_one_iff [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)] (i : ι) {x : G i} :
    mulSingle A i x ≠ 1 ↔ x ≠ 1 := by
  rw [← Subtype.coe_ne_coe]
  exact Pi.mulSingle_ne_one_iff

@[to_additive (attr := simp)]
lemma mulSingle_mul [∀ i, MulOneClass (G i)] [∀ i, OneMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r s : G i) :
    mulSingle A i r * mulSingle A i s = mulSingle A i (r * s) := by
  ext j
  obtain (rfl | hi) := em (i = j)
  · simp
  · simp [mulSingle_eq_of_ne' A _ hi]

@[simp]
lemma mul_single [∀ i, MulZeroClass (G i)] [∀ i, ZeroMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    x * single A i r = single A i ((x i) * r) := by
  ext j
  obtain (rfl | hi) := em (i = j)
  · simp
  · simp [single_eq_of_ne' A _ hi]

@[simp]
lemma single_mul [∀ i, MulZeroClass (G i)] [∀ i, ZeroMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    single A i r * x = single A i (r * (x i)) := by
  ext j
  obtain (rfl | hi) := em (i = j)
  · simp
  · simp [single_eq_of_ne' A _ hi]

end RestrictedProduct

end single

section openmap

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)]

-- Definitely need to review this.
lemma RestrictedProduct.isOpenMap_of_open_components
    (hCopen : ∀ i, IsOpen (C i : Set (G i))) (hDopen : ∀ i, IsOpen (D i : Set (H i)))
    (f : Πʳ i, [G i, C i] → Πʳ i, [H i, D i])
    (g : (i : ι) → G i → H i) (hcomponent : ∀ x i, f x i = g i (x i))
    (hg : ∀ i, IsOpenMap (g i))
    (hsurj : ∀ᶠ i in Filter.cofinite, Set.SurjOn (g i) (C i) (D i)) :
    IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  have hx := x.eventually
  let T := {i | ¬Set.SurjOn (g i) (C i) (D i) ∨ x i ∉ C i ∨ f x i ∉ D i}
  have hT : T.Finite := by
    unfold T
    rw [Set.setOf_or, Set.setOf_or]
    apply Set.Finite.union hsurj
    exact Set.Finite.union hx (f x).eventually
  rw [Filter.eventually_iff, ← Filter.le_principal_iff] at hsurj
  have hT' : Filter.cofinite ≤ Filter.principal Tᶜ := by
    rwa [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
  let x' : Πʳ i, [G i, C i]_[Filter.principal Tᶜ] :=
    ⟨fun i ↦ x i, by
      rw [Filter.eventually_principal]
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not, T] at hx
      exact hx.right.left⟩
  let y' : Πʳ i, [H i, D i]_[Filter.principal Tᶜ] :=
    ⟨fun i ↦ f x i, by
      rw [Filter.eventually_principal]
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not, T] at hx
      exact hx.right.right⟩
  have hinc : x = inclusion G C hT' x' := rfl
  have hinc' : f x = inclusion H D hT' y' := rfl
  rw [hinc', hinc, nhds_eq_map_inclusion hCopen hT', nhds_eq_map_inclusion hDopen hT',
    Filter.map_map, Filter.le_map_iff]
  intro U hU
  rw [Filter.mem_map, isEmbedding_coe_of_principal.nhds_eq_comap y', Filter.mem_comap]
  rw [isEmbedding_coe_of_principal.nhds_eq_comap x', Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hI, s, hs, hpi⟩ := ht
  use I.pi (fun i ↦ (g i) '' (s i ∩ (C i ∪ {x | i ∈ T}))) ∩ T.pi (fun i ↦ Set.range (g i))
  constructor
  · apply Filter.inter_mem
    · apply set_pi_mem_nhds hI
      intro i hi
      have : y' i = g i (x i) := by
        rw [← hcomponent]
        rfl
      rw [this]
      apply IsOpenMap.image_mem_nhds (hg i)
      apply Filter.inter_mem (hs i)
      by_cases h : i ∈ T
      · simp [h]
      · rw [eq_false h, Set.setOf_false, Set.union_empty]
        simp only [Set.mem_setOf_eq, not_or, not_not, T] at h
        apply (hCopen i).mem_nhds h.right.left
    · apply set_pi_mem_nhds hT
      intro i hi
      have : y' i = g i (x i) := by
        rw [← hcomponent]
        rfl
      rw [this]
      exact IsOpenMap.range_mem_nhds (hg i) (x i)
  · rintro y hy
    simp_rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_pi] at hy
    choose x₁ hx₁ using hy.left
    choose x₂ hx₂ using hy.right
    have : ∀ i, i ∉ T → ∃ (x : C i), (g i x) = (y i) := by
      intro i hi
      have hyi : (y i) ∈ (D i) := by
        have hy := y.prop
        rw [Filter.eventually_principal] at hy
        apply hy i hi
      simp only [Set.mem_setOf_eq, T] at hi
      push_neg at hi
      obtain ⟨x, hx, hxy⟩ := hi.left hyi
      exact ⟨⟨x, hx⟩, hxy⟩
    choose x₃ hx₃ using this
    classical
    let x (i : ι) := if h : i ∈ I then x₁ i h else
      if h' : i ∈ T then x₂ i h' else x₃ i h'
    refine ⟨⟨x, ?_⟩, ?_, ?_⟩
    · rw [Filter.eventually_principal]
      intro i hi
      unfold x
      by_cases h : i ∈ I
      · rw [dite_cond_eq_true (eq_true h)]
        have hmem := Set.mem_of_mem_inter_right (hx₁ i h).left
        rwa [eq_false hi, Set.setOf_false, Set.union_empty] at hmem
      · rw [dite_cond_eq_false (eq_false h), dite_cond_eq_false (eq_false hi)]
        exact Subtype.coe_prop (x₃ i hi)
    · apply htU
      rw [Set.mem_preimage]
      apply hpi
      simp only [SetLike.coe_sort_coe, Set.mem_pi, x]
      intro i hi
      simpa [dite_cond_eq_true (eq_true hi)] using Set.mem_of_mem_inter_left (hx₁ i hi).left
    · ext i
      simp only [SetLike.coe_sort_coe, Function.comp_apply, x, congrRight, map_apply, id_eq,
        inclusion, mk_apply]
      rw [hcomponent, mk_apply, mk_apply]
      by_cases h : i ∈ I
      · rw [dite_cond_eq_true (eq_true h)]
        exact (hx₁ i h).right
      · by_cases h' : i ∈ T
        · rw [dite_cond_eq_false (eq_false h), dite_cond_eq_true (eq_true h')]
          exact hx₂ i h'
        · rw [dite_cond_eq_false (eq_false h), dite_cond_eq_false (eq_false h')]
          exact hx₃ i h'

end openmap
