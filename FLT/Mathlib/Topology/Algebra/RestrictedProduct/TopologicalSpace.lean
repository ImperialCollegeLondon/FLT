import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import FLT.Mathlib.Topology.Algebra.ContinuousMonoidHom

open RestrictedProduct

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
  mapAlong_continuous G H id Filter.tendsto_id φ hφ hφcont

-- now let's add groups

section groups

variable {S T : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

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

end groups

section binary

variable {ι : Type*} {ℱ : Filter ι} {A B : ι → Type*}
  {C : (i : ι) → Set (A i)} {D : (i : ι) → Set (B i)}

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
  rw [continuous_rng_of_principal_pi]
  intro i
  rw [continuous_pi_iff]
  intro j
  exact (RestrictedProduct.continuous_eval i).comp (continuous_apply _)

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
    Πʳ i, [Matrix m n (A i), (C i).matrix] ≃ₜ Matrix m n (Πʳ i, [A i, C i]) :=
  (Homeomorph.restrictedProductPi (fun _ _ ↦ restrictedProductMatrix_aux _ hCopen)).trans
    (Homeomorph.piCongrRight fun _ ↦ Homeomorph.restrictedProductPi (fun _ ↦ hCopen))

lemma Homeomorph.restrictedProductMatrix_toEquiv {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    {C : (i : ι) → Set (A i)} (hCopen : ∀ i, IsOpen (C i)) :
    (restrictedProductMatrix hCopen).toEquiv =
      Equiv.restrictedProductMatrix (m := m) (n := n) :=
  rfl

/-- The structure map for a restricted product of monoids is a `MonoidHom`. -/
@[to_additive "The structure map for a restricted product of AddMonoids is an `AddMonoidHom`."]
def RestrictedProduct.structureMapMonoidHom {ι : Type*} (M : ι → Type*) [(i : ι) → Monoid (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)] (A : Π i, S i)
    (𝓕 : Filter ι) : ((i : ι) → (A i)) →* Πʳ (i : ι), [M i, Submonoid.ofClass (A i)]_[𝓕] where
  toFun := structureMap M (A ·) 𝓕
  map_one' := rfl
  map_mul' := by intros; rfl

open MulOpposite MonoidHom Units Equiv Set in
/-- The equivalence `Submonoid.unitsEquivUnitsType`, for monoids equipped with a topology. -/
@[to_additive "The equivalence `AddSubmonoid.addUnitsAddEquivUnitsType`, for monoids equipped with
a topology."]
def Submonoid.unitsContinuousMulEquivUnitsType {M : Type*} [TopologicalSpace M] [Monoid M]
    {S : Submonoid M} (hS : IsOpen (S : Set M)) : S.units ≃ₜ* Sˣ where
  toMulEquiv := S.unitsEquivUnitsType
  continuous_toFun := {
    isOpen_preimage U hU := by
      obtain ⟨t, ht, rfl⟩ := isInducing_embedProduct.isOpen_iff.mpr hU
      let g : Sˣ →* Mˣ := Units.map S.subtype
      have hg : IsOpenMap g := isOpenMap_map (by simp) hS.isOpenMap_subtype_val
      refine ⟨g '' (embedProduct S ⁻¹' t), hg _ (isOpen_induced ht), Set.ext fun s ↦ ?_⟩
      simp only [mem_preimage, mem_image, embedProduct_apply, inv_mk, coeHom_apply, g,
        unitsEquivUnitsType]
      exact ⟨fun ⟨_, ⟨h₁, h₂⟩⟩ ↦ by simp [← h₂, h₁],
        fun h ↦ ⟨S.unitsEquivUnitsType s, by simp [unitsEquivUnitsType, h]⟩⟩
  }
  continuous_invFun := {
    isOpen_preimage U hU := by
      obtain ⟨t, ⟨V, hV, rfl⟩, rfl⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mpr hU
      let f : S × Sᵐᵒᵖ → M × Mᵐᵒᵖ := Prod.map Subtype.val (op ∘ Subtype.val ∘ unop)
      have hf : Continuous f := continuous_subtype_val.fst'.prodMk <| continuous_op.comp' <|
        continuous_subtype_val.comp' <| continuous_unop.comp' continuous_snd
      exact ⟨f ⁻¹' V, hf.isOpen_preimage V hV, rfl⟩
  }

/-- The monoid homeomorphism between the units of a restricted product of topological monoids
and the restricted product of the units of the monoids, when the products are with
respect to open submonoids.
-/
def ContinuousMulEquiv.restrictedProductUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)]
    [(i : ι) → ContinuousMul (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)]
    (A : Π i, S i) (hA : ∀ i, IsOpen (A i : Set (M i))) :
    (Πʳ i, [M i, A i])ˣ ≃ₜ*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units] :=
    have : Fact (∀ i, IsOpen (A i : Set (M i))) := Fact.mk hA
    have hA' : ∀ i, IsOpen ((Submonoid.ofClass (A i)).units : Set (M i)ˣ) :=
      fun i ↦ Submonoid.units_isOpen (hA i)
    have : Fact (∀ i, IsOpen ((Submonoid.ofClass (A i)).units : Set (M i)ˣ)) := Fact.mk hA'
    -- The key idea is that `MulEquiv.restrictedProductUnits ∘ (Units.map sM) = sMx ∘ g ∘ f`,
    -- where `Units.map sM`, `sMx`, `g`, and `f` (defined below) are all local homeomorphisms.
    let sM := structureMapMonoidHom M A cofinite
    let f : ((i : ι) → (A i))ˣ ≃ₜ ((i : ι) → (A i)ˣ) := ContinuousMulEquiv.piUnits.toHomeomorph
    let g : ((i : ι) → (Submonoid.ofClass (A i))ˣ) ≃ₜ ((i : ι) → (Submonoid.ofClass (A i)).units) :=
      Homeomorph.piCongrRight fun i ↦
        (Submonoid.unitsContinuousMulEquivUnitsType (hA i)).symm.toHomeomorph
    let sMx := structureMap (fun i ↦ (M i)ˣ) (fun i ↦ (Submonoid.ofClass (A i)).units) cofinite
  {
  __ := MulEquiv.restrictedProductUnits
  continuous_toFun := by
    apply continuous_of_continuousAt_one MulEquiv.restrictedProductUnits
    intro N hN
    have hN' : (f.trans g) ⁻¹' (sMx ⁻¹' N) ∈ nhds 1 := (f.trans g).continuous.continuousAt
      |>.preimage_mem_nhds <| isEmbedding_structureMap.continuous.continuousAt.preimage_mem_nhds hN
    apply mem_of_superset <| Units.isOpenMap_map (f := sM) isEmbedding_structureMap.injective
      (isOpenEmbedding_structureMap hA).isOpenMap |>.image_mem_nhds hN'
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  continuous_invFun := by
    apply continuous_of_continuousAt_one MulEquiv.restrictedProductUnits.symm
    intro N hN
    have hN' : (Units.map sM) ⁻¹' N ∈ nhds 1 :=
      Units.continuous_map isEmbedding_structureMap.continuous |>.continuousAt.preimage_mem_nhds hN
    apply mem_of_superset <| (isOpenEmbedding_structureMap hA').isOpenMap.image_mem_nhds <|
      (f.trans g).isOpenMap.image_mem_nhds hN'
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hx
      }

/-- The monoid homeomorphism between a restricted product of n x n matrices, and n x n matrices
of restricted products, when the products are with respect to open sets.
-/
def ContinuousMulEquiv.restrictedProductMatrix {ι : Type*}
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, Ring (A i)]
    {C : (i : ι) → Subring (A i)} (hCopen : ∀ i, IsOpen ((C i) : Set (A i))) :
    Matrix n n (Πʳ i, [A i, C i]) ≃ₜ*
      Πʳ i, [Matrix n n (A i), ((C i).matrix : Subring (Matrix n n (A i)))] :=
    let restrictedProductMatrix :
        Matrix n n (Πʳ i, [A i, C i]) ≃ₜ
          Πʳ i, [Matrix n n (A i), ((C i).matrix : Subring (Matrix n n (A i)))] :=
      Homeomorph.symm (Homeomorph.restrictedProductMatrix hCopen)
  {
  __ := restrictedProductMatrix
  map_mul' x y := by
    ext i j k
    rw [mul_apply, Matrix.mul_apply]
    have h {x : Matrix n n Πʳ (i : ι), [A i, ↑(C i)]} {i : ι} {j k : n} :
        (restrictedProductMatrix.toFun x) i j k = (x j k) i := by
      simp [restrictedProductMatrix, Homeomorph.restrictedProductMatrix,
        Homeomorph.restrictedProductPi, Equiv.restrictedProductPi, Matrix]
    simp only [h, Matrix.mul_apply]
    conv_rhs => arg 2; intro _; rw [← mul_apply]
    apply map_sum (RestrictedProduct.evalAddMonoidHom _ _) _ _
      }

/-- The monoid homeomorphism between the matrix units over a restricted product
and the restricted product of the matrix units over the factors,
when the products are with respect to open submonoids.
-/
def ContinuousMulEquiv.restrictedProductMatrixUnits {ι : Type*}
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : ι → Type*} [∀ i, TopologicalSpace (A i)] [∀ i, Ring (A i)] [∀ i, IsTopologicalRing (A i)]
    {C : (i : ι) → Subring (A i)} (hCopen : ∀ i, IsOpen ((C i) : Set (A i))) :
    (Matrix n n (Πʳ i, [A i, C i]))ˣ ≃ₜ*
      Πʳ i, [(Matrix n n (A i))ˣ, ((C i).matrix.units : Subgroup (Matrix n n (A i))ˣ)] :=
  (ContinuousMulEquiv.restrictedProductMatrix hCopen).units_map.trans
    (ContinuousMulEquiv.restrictedProductUnits (fun i => (C i).matrix) (fun i => (hCopen i).matrix))

end pi

section flatten

variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)
variable (hf : Filter.comap f 𝒢 = ℱ)

namespace RestrictedProduct

variable [Π i, TopologicalSpace (G i)]

/-- The canonical homeomorphism from a restricted product of products over fibres of a map on
indexing sets to the restricted product over the original indexing set. -/
def flatten_homeomorph :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃ₜ
    Πʳ i, [G i, C i]_[ℱ] where
  __ := flatten_equiv C hf
  continuous_toFun := by
    dsimp only [flatten_equiv]
    apply mapAlong_continuous
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
      fun x ↦ ⟨fun _ i ↦ x i, by
        have : Filter.comap f (Filter.principal T) ≤ Filter.principal S := by
          rw [Filter.le_principal_iff, Filter.mem_comap]
          use T
          refine ⟨Filter.mem_principal_self T, ?_⟩
          rw [hTval, Set.preimage_compl, Set.compl_subset_comm]
          apply Set.subset_preimage_image
        have hx := Filter.Eventually.filter_mono this x.prop
        rw [Filter.eventually_comap] at hx
        filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
    let hg: Continuous g := by
      rw [continuous_rng_of_principal]
      unfold g
      fun_prop
    apply (continuous_inclusion hT).comp hg

@[simp]
lemma flatten_homeomorph_apply (x) (i : ι) :
    flatten_homeomorph C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_homeomorph_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_homeomorph C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

/-- The homeomorphism given by `flatten` when both restricted products are over the cofinite
filter and there's a topology on the factors. -/
def flatten_homeomorph' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃ₜ
    Πʳ i, [G i, C i] :=
  flatten_homeomorph C <|
    le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

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

section nhds

open scoped Filter

variable [Π i, TopologicalSpace (G i)]

/-- An explicit condition for a set to be in the neighborhood of `x : Πʳ i, [G i, C i]_[𝓟 T]`
in terms of a product of neighbourhoods on the factors. -/
lemma RestrictedProduct.mem_nhds_iff_of_principal {T : Set ι} {x : Πʳ i, [G i, C i]_[𝓟 T]}
    (U : Set Πʳ i, [G i, C i]_[𝓟 T]) :
    U ∈ nhds x ↔ ∃ (I : Set ι) (s : (i : ι) → Set (G i)), I.Finite ∧ (∀ i, s i ∈ nhds (x i)) ∧
    (↑) ⁻¹' I.pi s ⊆ U := by
  rw [isEmbedding_coe_of_principal.nhds_eq_comap, Filter.mem_comap, nhds_pi]
  simp_rw [Filter.mem_pi]
  exact ⟨fun ⟨t, ⟨I, hIf, s, hs, ht⟩, htU⟩ ↦ ⟨I, s, hIf, hs, by grw [ht, htU]⟩,
    fun ⟨I, s, hIf, hs, hU⟩ ↦ ⟨I.pi s, ⟨I, hIf, s, hs, subset_rfl⟩, hU⟩⟩


/-- A condition for a set to be a neighborhood in `Πʳ i, [G i, C i]`, slightly weaker than the
condition in `mem_nhds_iff_of_cofinite`. -/
lemma RestrictedProduct.mem_nhds_of_exists_nhds_of_cofinite {x : Πʳ i, [G i, C i]}
    {U : Set Πʳ i, [G i, C i]} (hCopen : ∀ i, IsOpen (C i : Set (G i))) (s : (i : ι) → Set (G i))
    (hs : ∀ i, s i ∈ nhds (x i)) (hf : ∀ᶠ i in Filter.cofinite, C i ⊆ s i)
    (hU : (↑) ⁻¹' Set.univ.pi s ⊆ U) : U ∈ nhds x := by
  set I := {i | ¬C i ⊆ s i} with hIval
  set T := {i | x i ∉ C i} with hTval
  have hT : Filter.cofinite ≤ Filter.principal Tᶜ := by simpa using x.eventually
  have hT' : ∀ᶠ (i : ι) in Filter.principal Tᶜ, x i ∈ C i := by simp [hTval]
  obtain ⟨x', hx⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually G C hT hT'
  have hs' : ∀ i, s i ∈ nhds (x' i) := by simpa [← hx] using hs
  rw [← hx, nhds_eq_map_inclusion hCopen hT, Filter.mem_map, mem_nhds_iff_of_principal]
  refine ⟨I ∪ T, s, Set.Finite.union hf x.eventually, hs', ?_⟩
  grw [← hU, ← Set.preimage_comp, coe_comp_inclusion, ← Set.image_subset_iff,
      Set.image_preimage_eq_inter_range, range_coe_principal]
  rintro y hy i -
  simp only [Set.mem_inter_iff, Set.mem_pi] at hy
  by_cases h : i ∈ I ∪ T
  · apply hy.left i h
  · simp only [Set.mem_union, not_or] at h
    have hy' : y i ∈ C i := hy.right i h.right
    simp only [hIval, Set.mem_setOf_eq, not_not] at h
    exact h.left hy'

/-- The classical condition for a set to be a neighborhood in the restricted product. -/
lemma RestrictedProduct.mem_nhds_iff_of_cofinite {x : Πʳ i, [G i, C i]} {U : Set Πʳ i, [G i, C i]}
    (hCopen : ∀ i, IsOpen (C i : Set (G i))) :
    U ∈ nhds x ↔ ∃ (s : (i : ι) → Set (G i)), (∀ i, s i ∈ nhds (x i)) ∧
    (∀ᶠ i in Filter.cofinite, s i = C i) ∧ Set.univ.pi s ⊆ (↑) '' U := by
  refine ⟨fun hn ↦ ?_, fun ⟨s, hs, hsf, hsU⟩ ↦ ?_⟩
  · set T := {i | x i ∉ C i} with hTval
    have hT : Filter.cofinite ≤ Filter.principal Tᶜ := by simpa using x.eventually
    have hT' : ∀ᶠ (i : ι) in Filter.principal Tᶜ, x i ∈ C i := by simp [hTval]
    obtain ⟨x', hx⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually G C hT hT'
    rw [← hx, nhds_eq_map_inclusion hCopen hT, Filter.mem_map, mem_nhds_iff_of_principal] at hn
    obtain ⟨I, s, hIf, hs, hU⟩ := hn
    refine ⟨fun i ↦ (s i ∪ {x | i ∉ I}) ∩ (C i ∪ {x | i ∈ T}), ?_, ?_, ?_⟩
    · intro i
      rw [← hx]
      apply Filter.inter_mem (Filter.mem_of_superset (hs i) Set.subset_union_left)
      apply IsOpen.mem_nhds (IsOpen.union (hCopen i) isOpen_const)
      rw [Set.mem_union, Set.mem_setOf_eq, or_iff_not_imp_right]
      apply x'.eventually
    · filter_upwards [hIf.compl_mem_cofinite, x.eventually] with i (hI : i ∉ I) hC
      simp [hI, hC, hTval]
    · grw [← image_coe_preimage_inclusion_subset, ← hU, Set.image_preimage_eq_inter_range,
        range_coe_principal]
      simp [Set.subset_def, or_iff_not_imp_right, forall_and]
  · apply mem_nhds_of_exists_nhds_of_cofinite hCopen s hs
    · filter_upwards [hsf] with _ using superset_of_eq
    · exact Set.preimage_subset hsU DFunLike.coe_injective.injOn

end nhds

section openmap

variable [Π i, TopologicalSpace (G i)] [Π i, TopologicalSpace (H i)]

lemma RestrictedProduct.isOpenMap_of_open_components
    (hCopen : ∀ i, IsOpen (C i : Set (G i))) (hDopen : ∀ i, IsOpen (D i : Set (H i)))
    (f : Πʳ i, [G i, C i] → Πʳ i, [H i, D i]) (g : (i : ι) → G i → H i)
    (hcomponent : ∀ x i, f x i = g i (x i)) (hg : ∀ i, IsOpenMap (g i))
    (hsurj : ∀ᶠ i in Filter.cofinite, Set.SurjOn (g i) (C i) (D i)) :
    IsOpenMap f := by
  refine IsOpenMap.of_nhds_le fun x ↦ Filter.le_map fun U hU ↦ ?_
  obtain ⟨s, hf, hs, hU⟩ := (mem_nhds_iff_of_cofinite hCopen).mp hU
  apply mem_nhds_of_exists_nhds_of_cofinite hDopen fun i ↦ (g i) '' (s i)
  · intro i
    rw [hcomponent]
    exact IsOpenMap.image_mem_nhds (hg i) (hf i)
  · filter_upwards [hsurj, hs] with i hsurj' heq using heq ▸ hsurj'
  · apply Set.preimage_subset _ DFunLike.coe_injective.injOn
    grw [← Set.piMap_image_univ_pi, hU, ← Set.image_comp,
      ← Set.image_comp, ← components_comp_coe_eq_coe_apply hcomponent]
    rfl

end openmap
