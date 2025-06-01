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

@[to_additive (attr := simp)]
lemma mul_apply {S : ι → Type*} [(i : ι) → SetLike (S i) (R i)] {B : (i : ι) → S i}
    [(i : ι) → Mul (R i)] [∀ (i : ι), MulMemClass (S i) (R i)]
    (x y : Πʳ (i : ι), [R i, ↑(B i)]_[ℱ]) (i : ι) : (x * y) i = x i * y i := rfl

@[simp] lemma eventually (x : Πʳ i, [R i, A i]_[ℱ]) : ∀ᶠ i in ℱ, x i ∈ A i := x.2

variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}
variable {ℱ : Filter ι}

@[simp]
lemma one_apply [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] {i : ι} :
  (1 : Πʳ i, [R i, B i]_[ℱ]) i = 1 := rfl

-- I'm avoiding using these if possible

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

-- TODO: this attribute should be in mathlib
attribute [fun_prop] RestrictedProduct.continuous_inclusion

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)] in
@[fun_prop]
theorem Continuous.restrictedProduct_congrRight {φ : (i : ι) → G i → H i}
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (C i) (D i))
    (hφcont : ∀ i, Continuous (φ i)) :
    Continuous (congrRight φ hφ) :=
  Continuous.restrictedProduct_map Filter.tendsto_id hφ hφcont

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

@[fun_prop]
lemma Equiv.continuous_restrictedProductProd_symm {S : Set ι}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)] :
    Continuous (Equiv.restrictedProductProd (C := C) (D := D) (ℱ := .principal S)).symm := by
  simp only [restrictedProductProd, coe_fn_symm_mk]
  rw [continuous_rng_of_principal]
  -- this proof is doing something a little suspicious, but it's not clear what
  -- I'm relying on the topological properties of the restricted product on a principal filter
  -- so maybe we need more lemmas about that
  -- eg each projection `Πʳ i, [A i, C i]_[.principal S] → A i` is continuous
  change Continuous (fun i ↦ fun j ↦ (_, _))
  rw [continuous_pi_iff]
  intro i
  rw [continuous_prodMk]
  constructor
  · exact ((continuous_apply i).comp isEmbedding_coe_of_principal.continuous).comp continuous_fst
  · exact ((continuous_apply i).comp isEmbedding_coe_of_principal.continuous).comp continuous_snd

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


-- Q: Is there a mathlibism for `{f | ∀ j, f j ∈ C j i}`?
-- A: Yes, `Set.pi Set.univ`, except that it's defeq to `{f | ∀ j ∈ univ, f j ∈ C j i}`

/-- The bijection between a restricted product of finite products, and a finite product
of restricted products.
-/
def Equiv.restrictedProductPi {ι : Type*} {ℱ : Filter ι} {n : Type*} [Fintype n]
    {A : n → ι → Type*}
    {C : (j : n) → (i : ι) → Set (A j i)} :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}]_[ℱ] ≃ Π j, Πʳ i, [A j i, C j i]_[ℱ] where
      toFun x j := .mk (fun i ↦ x i j) (by filter_upwards [x.2] with i h using h j)
      invFun y := .mk (fun i j ↦ y j i) (by simp)
      left_inv x := by ext; rfl
      right_inv y := by ext; rfl

/-- The homeomorphism between a restricted product of finite products, and a finite product
of restricted products, when the products are with respect to open subsets.
-/
@[nolint unusedArguments] -- finiteness will be used when #569 sorry is filled in
-- and then this can be removed
def Homeomorph.restrictedProductPi {ι : Type*} {n : Type*} [Fintype n]
    {A : n → ι → Type*} [∀ j i, TopologicalSpace (A j i)]
    {C : (j : n) → (i : ι) → Set (A j i)} (hCopen : ∀ j i, IsOpen (C j i)) :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}] ≃ₜ Π j, (Πʳ i, [A j i, C j i]) where
  __ := Equiv.restrictedProductPi
  continuous_toFun := by
    simp only [Equiv.restrictedProductPi, Set.mem_setOf_eq, Equiv.toFun_as_coe, Equiv.coe_fn_mk,
      continuous_pi_iff]
    simp +singlePass only [RestrictedProduct.continuous_dom]
    intro i S hS
    let f : Πʳ i, [(j : n) → A j i, {f | ∀ j, f j ∈ C j i}]_[.principal S] → _ :=
      inclusion (A i) (C i) hS ∘ congrRight (fun j t ↦ t i) (by simp +contextual [Set.MapsTo])
    convert_to Continuous f
    fun_prop
  continuous_invFun := by
    sorry

/-- The bijection between a restricted product of m x n matrices, and m x n matrices
of restricted products.
-/
def Equiv.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*}
    {C : (i : ι) → Set (A i)} :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ Matrix m n (Πʳ i, [A i, C i])  where
      toFun x a b := ⟨fun i ↦ x i a b, by filter_upwards [x.2] with i h using h a b⟩
      invFun y := ⟨fun i a b ↦ y a b i, (by simp [- Filter.eventually_cofinite])⟩
      left_inv x := by ext; rfl
      right_inv y := by ext; rfl

/-- The homeomorphism between a restricted product of m x n matrices, and m x n matrices
of restricted products, when the products are with respect to open sets.
-/
@[nolint unusedArguments] -- openness will be used when #571 sorry is filled in
-- and then this can be removed
def Homeomorph.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    {C : (i : ι) → Set (A i)} (hCopen : ∀ i, IsOpen (C i)) :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ₜ Matrix m n (Πʳ i, [A i, C i])  where
      __ := Equiv.restrictedProductMatrix
      continuous_toFun := sorry  --#571
      continuous_invFun := sorry --#571

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
