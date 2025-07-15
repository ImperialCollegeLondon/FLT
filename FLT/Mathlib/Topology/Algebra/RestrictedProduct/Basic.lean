import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.Matrix
import FLT.Mathlib.Topology.Algebra.Group.Units
import FLT.Mathlib.Topology.Algebra.Constructions

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι → Type*} {A : (i : ι) → Set (R i)}
variable {ℱ : Filter ι}

section inclusion

@[simp]
lemma coe_comp_inclusion {𝒢 : Filter ι} (h : ℱ ≤ 𝒢) :
    DFunLike.coe ∘ inclusion R A h = DFunLike.coe :=
  rfl

@[simp]
lemma inclusion_apply {𝒢 : Filter ι} (h : ℱ ≤ 𝒢) {x : Πʳ i, [R i, A i]_[𝒢]} (i : ι) :
    inclusion R A h x i = x i :=
  rfl

lemma image_coe_preimage_inclusion_subset {𝒢 : Filter ι} (h : ℱ ≤ 𝒢)
    (U : Set Πʳ i, [R i, A i]_[ℱ]) : (⇑) '' (inclusion R A h ⁻¹' U) ⊆ (⇑) '' U :=
  fun _ ⟨x, hx, hx'⟩ ↦ ⟨inclusion R A h x, hx, hx'⟩

end inclusion

variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

variable
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

/-- The maps between restricted products over a fixed index type,
given maps on the factors. -/
def congrRight (φ : (i : ι) → G i → H i)
    (hφ : ∀ᶠ i in ℱ, Set.MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[ℱ]) : (Πʳ i, [H i, D i]_[ℱ]) :=
  map φ hφ x

end RestrictedProduct

open RestrictedProduct

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

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
    (hU : SubmonoidClass.isProductAt U i) (hg : mulSupport g ⊆ {i}) (γ : Πʳ i, [G i, A i])
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
    simp only [smul_eq_mul, mul_assoc, mul_inv_cancel_left, hcomm]⟩,
    mulSupport_mul_subset huᵢ hg⟩

end RestrictedProduct

end supports

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

/-- The bijection between a restricted product of m x n matrices, and m x n matrices
of restricted products.
-/
def Equiv.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*}
    {C : (i : ι) → Set (A i)} :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ Matrix m n (Πʳ i, [A i, C i]) :=
  Equiv.restrictedProductPi.trans (Equiv.piCongrRight fun _ ↦ Equiv.restrictedProductPi)

end pi

section flatten

namespace RestrictedProduct

variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)

variable (hf : Filter.Tendsto f ℱ 𝒢) in
/-- The canonical map from a restricted product of products over fibres of a map on indexing sets
to the restricted product over the original indexing set. -/
def flatten : Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] →
    Πʳ i, [G i, C i]_[ℱ] :=
  mapAlong _ G f hf (fun i x ↦ x ⟨i, rfl⟩) (by filter_upwards with x y hy using hy ⟨x, rfl⟩ trivial)

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

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

/-- The equivalence given by `flatten` when both restricted products are over the cofinite
filter. -/
def flatten_equiv' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃
    Πʳ i, [G i, C i] :=
  flatten_equiv C <| le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

@[simp]
lemma flatten_equiv'_apply (x) (i : ι) :
    flatten_equiv' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_equiv' C hf).symm x i j = x j.1 :=
  rfl

end RestrictedProduct

end flatten

section single

namespace RestrictedProduct

variable {S : ι → Type*}
variable [Π i, SetLike (S i) (G i)]
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
  obtain (rfl | hne) := em (i = j)
  · simp
  · simp [mulSingle_eq_of_ne' A _ hne]

@[simp]
lemma mul_single [∀ i, MulZeroClass (G i)] [∀ i, ZeroMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    x * single A i r = single A i ((x i) * r) := by
  ext j
  obtain (rfl | hne) := em (i = j)
  · simp
  · simp [single_eq_of_ne' A _ hne]

@[simp]
lemma single_mul [∀ i, MulZeroClass (G i)] [∀ i, ZeroMemClass (S i) (G i)]
    [∀ i, MulMemClass (S i) (G i)] (i : ι) (r : G i) (x : Πʳ i, [G i, A i]) :
    single A i r * x = single A i (r * (x i)) := by
  ext j
  obtain (rfl | hne) := em (i = j)
  · simp
  · simp [single_eq_of_ne' A _ hne]

end RestrictedProduct

end single

section components

namespace RestrictedProduct

variable {ι₂ : Type*} {f : ι₂ → ι} {𝒢 : Filter ι₂}
variable {G₂ : ι₂ → Type*} {C₂ : (i : ι₂) → Set (G₂ i)}
variable (hf : 𝒢 = Filter.comap f ℱ)
variable (φ : Πʳ i, [G i, C i]_[ℱ] → Πʳ i, [G₂ i, C₂ i]_[𝒢])
variable (g : (j : ι₂) → G (f j) → G₂ j) (hcomponent : ∀ x j, φ x j = g j (x (f j)))

include hcomponent in
variable {φ} {g} in
lemma components_comp_coe_eq_coe_apply : (fun a j ↦ g j (a (f j))) ∘ (⇑) = (⇑) ∘ φ := by
  ext x i
  simp [hcomponent]

lemma exists_update (x : Πʳ i, [G i, C i]_[ℱ]) (i : ι) (a : G i)
    (h : {i}ᶜ ∈ ℱ) : ∃ y : Πʳ i, [G i, C i]_[ℱ], y i = a ∧ ∀ j ≠ i, y j = x j := by
  have hy' (j : ι) : ∃ y : G j, (j = i → y ≍ a) ∧ (j ≠ i → y = x j) := by
    obtain (rfl | hne) := em (j = i)
    · exact ⟨a, fun _ ↦ HEq.rfl, nofun⟩
    · exact ⟨x j, fun heq ↦ absurd heq hne, fun _ ↦ rfl⟩
  choose y hy using hy'
  refine ⟨⟨y, ?_⟩, eq_of_heq ((hy i).left rfl), fun j ↦ (hy j).right⟩
  rw [← Filter.eventually_mem_set] at h
  filter_upwards [h, x.eventually] with j hj hx
  rwa [(hy j).right hj]

variable (C) in
lemma exists_apply_eq [∀ i, Nonempty (C i)] (i : ι) (a : G i) (h : {i}ᶜ ∈ ℱ) :
    ∃ x : Πʳ i, [G i, C i]_[ℱ], x i = a := by
  let y : Πʳ i, [G i, C i]_[ℱ] := ⟨fun i ↦ (Classical.choice inferInstance : C i),
    Filter.Eventually.of_forall (fun x ↦ Subtype.coe_prop _)⟩
  obtain ⟨x, hx, -⟩ := exists_update y i a h
  exact ⟨x, hx⟩

variable [∀ j, Nonempty (C₂ j)]

include hcomponent in
lemma surjective_components_of_surjective (hφ : Function.Surjective φ) (j : ι₂) (hj : {j}ᶜ ∈ 𝒢) :
    Function.Surjective (g j) := by
  intro y
  obtain ⟨y', hy'⟩ := exists_apply_eq C₂ j y hj
  obtain ⟨x, hx⟩ := hφ y'
  use (x (f j))
  rw [← hcomponent, hx, hy']

include hf hcomponent in
lemma eventually_surjOn_of_surjective (hφ : Function.Surjective φ) :
    ∀ᶠ (j : ι₂) in 𝒢, Set.SurjOn (g j) (C (f j)) (C₂ j) := by
  classical
  have p (j : ι₂) : ∃ (y : C₂ j), (∃ (x : C (f j)), g j x = y)
       → Set.SurjOn (g j) (C (f j)) (C₂ j) := by
    by_cases hsurj : Set.SurjOn (g j) (C (f j)) (C₂ j)
    · exact ⟨Classical.choice inferInstance, fun _ ↦ hsurj⟩
    · rw [Set.SurjOn, Set.not_subset_iff_exists_mem_notMem] at hsurj
      obtain ⟨y, hy, hne⟩ := hsurj
      exact ⟨⟨y, hy⟩, fun ⟨⟨x, hx⟩, hxy⟩ ↦ absurd ⟨x, hx, hxy⟩ hne⟩
  choose y' hy' using p
  set y : Πʳ i, [G₂ i, C₂ i]_[𝒢] :=
    ⟨fun i ↦ y' i, Filter.Eventually.of_forall (fun i ↦ (y' i).prop)⟩ with hy
  obtain ⟨x, hx⟩ := hφ y
  rw [hf, Filter.eventually_comap]
  filter_upwards [x.eventually]
  rintro - hx' j rfl
  apply hy'
  use ⟨x (f j), hx'⟩
  rw [← hcomponent, hx, hy, mk_apply]

end RestrictedProduct

end components
