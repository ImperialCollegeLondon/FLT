import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Topology.Algebra.Module.Basic

/-!

# The module topology

If `R` is a topological ring and `M` is an `R`-module, the *module topology* on `M` is
the finest topology making all `R`-linear maps `Rⁿ → M` continuous. Here `n` runs through
the naturals and `Rⁿ` has the product topology. This topology has some nice properties.
For example if `D` is an `R`-algebra which is finite as an `R`-module, then `D` is
automatically a topological ring for the module topology.

## Details

If `R` is a topological ring and `A` is an `R`-module, then there are several ways in which
`A` can inherit a topology from `R` via the action (indeed, this is the 4th one which
the author has tried). We make one such definition here, which we call the *module* topology,
or the `R`-module topology if there is an ambiguity.

The module topology has some nice properties: for example all `R`-linear maps between modules
are automatically continuous for the module topology. On the category of finite `R`-modules
things are even better. Given any `R`-linear surjection `Rⁿ → A` for `n` a natural (or a
finite type), the topology on `A` is the pushforward (i.e. `TopologicalSpace.coinduced`)
of the product topology on `Rⁿ`. If furthermore `R` is commutative and `A` is an `R`-algebra
which is finite as an `R`-module, then `A` automatically becomes a topological ring for the
module topology (i.e., multiplication is continuous). This can be very convenient (for example
it can be used to topologise finite-dimensional central simple algebras over the reals
or $p$-adics).

-/

section elsewhere

variable {A : Type*} [AddCommGroup A] [τA : TopologicalSpace A] [ContinuousAdd A]
variable {B : Type*} [AddCommGroup B] [τB : TopologicalSpace B]

lemma AddMonoidHom.sub_mem_ker_iff {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (φ : A →+ B) {x y : A} :
    x - y ∈ AddMonoidHom.ker φ ↔ φ x = φ y := by
  rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]

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

def LinearMap.neg (R : Type*) [Ring R] (A : Type*) [AddCommGroup A] [Module R A] : A →ₗ[R] A where
  toFun := (-·)
  map_add' := neg_add
  map_smul' r a := (smul_neg r a).symm

end elsewhere

section basics

variable (R : Type*) [TopologicalSpace R] [Ring R] [TopologicalRing R]
variable (A : Type*) [AddCommMonoid A] [Module R A]

/- The module topology on an `R`-module `M` is the finest topology
which makes all `R`-linear maps `Rⁿ →ₗ[R] M` continuous.
-/
abbrev moduleTopology : TopologicalSpace A :=
  ⨆ (n : ℕ), ⨆ (φ : (Fin n → R) →ₗ[R] A), .coinduced φ inferInstance

/-
`IsModuleTopology R A` is a propositional typclass carrying around a proof that the topology
on `A` is the `R`-module topology.-/
class IsModuleTopology [τA : TopologicalSpace A] : Prop where
  isModuleTopology' : τA = moduleTopology R A

-- because default binders for isModuleTopology' are wrong and currently
-- there is no way to change this. There's a Lean 4 issue for this IIRC **TODO** where?
lemma isModuleTopology [τA : TopologicalSpace A] [IsModuleTopology R A] :
    τA = moduleTopology R A :=
  IsModuleTopology.isModuleTopology' (R := R) (A := A)

end basics

namespace ModuleTopology

section one

variable (R : Type*) [Ring R] [τ : TopologicalSpace R] [TopologicalRing R]

instance instId : IsModuleTopology R R where
  isModuleTopology' := le_antisymm (le_iSup_of_le 1 <| le_iSup_of_le (LinearMap.proj 0)
    (fun U hU ↦ Continuous.isOpen_preimage (f := fun r ↦ fun _ ↦ r) (by fun_prop) _
      (isOpen_coinduced.1 hU))) <|
    iSup_le fun _ ↦ iSup_le fun φ ↦ continuous_iff_coinduced_le.1 <| LinearMap.continuous_on_pi φ

instance instPiNat (n : ℕ) : IsModuleTopology R (Fin n → R) where
  isModuleTopology' :=
    le_antisymm (le_iSup_of_le n <| le_iSup_of_le (LinearMap.id) <| by rfl) <|
      iSup_le fun _ ↦ iSup_le fun φ ↦ (LinearMap.continuous_on_pi φ).coinduced_le

instance instPiFinite (ι : Type*) [Finite ι] : IsModuleTopology R (ι → R) where
  isModuleTopology' :=
    le_antisymm (le_iSup_of_le (Nat.card ι) <| le_iSup_of_le
      (LinearMap.funLeft _ _ ((Finite.equivFin ι))) <| ge_of_eq <| Homeomorph.coinduced_eq
      (Homeomorph.piCongrLeft (Y := fun _ ↦ R) (Finite.equivFin ι)).symm) <|
      iSup_le fun _ ↦ iSup_le fun φ ↦ (LinearMap.continuous_on_pi φ).coinduced_le

end one

section function

variable {R : Type*} [τR : TopologicalSpace R] [Ring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
@[continuity, fun_prop]
lemma continuous_of_linearMap (f : A →ₗ[R] B) : Continuous f := by
  rw [isModuleTopology R A, isModuleTopology R B, continuous_iff_le_induced]
  apply iSup_le <| fun n ↦ iSup_le <| fun φ ↦ ?_
  rw [← coinduced_le_iff_le_induced, coinduced_compose]
  exact le_iSup_of_le n <| le_iSup_of_le (f.comp φ) le_rfl

-- should this be in the API?
lemma continuous_of_linearMap' {A : Type*} [AddCommMonoid A] [Module R A]
    {B : Type*} [AddCommMonoid B] [Module R B] (f : A →ₗ[R] B) :
    @Continuous _ _ (moduleTopology R A) (moduleTopology R B) f := by
  letI : TopologicalSpace A := moduleTopology R A
  letI : TopologicalSpace B := moduleTopology R B
  haveI : IsModuleTopology R A := ⟨rfl⟩
  haveI : IsModuleTopology R B := ⟨rfl⟩
  fun_prop

def homeo_of_linearEquiv [IsModuleTopology R A] [IsModuleTopology R B] (f : A ≃ₗ[R] B) : A ≃ₜ B where
  toFun := f
  invFun := f.symm
  left_inv := LinearEquiv.symm_apply_apply f
  right_inv := LinearEquiv.apply_symm_apply f
  continuous_toFun := continuous_of_linearMap f.toLinearMap
  continuous_invFun := continuous_of_linearMap f.symm.toLinearMap

-- lemma _root_.ContinuousLinearEquiv.isModuleTopology [IsModuleTopology R A]
--     {B : Type*} [AddCommMonoid B] [Module R B] [TopologicalSpace B] (e : A ≃L[R] B) :
--   IsModuleTopology R B where
--     isModuleTopology' :=
--       let e' := e.toLinearEquiv
--       let e'' := (e.toHomeomorph : A ≃ₜ B)
--       let this : _ ≃ₜ _ := homeo_of_linearEquiv (aB := moduleTopology R B) e'
--       --R _ _ B _ _ (moduleTopology R B)
--       let bid : @Homeomorph B B  := this.symm.trans e''--(e.toHomeomorph : A ≃ₜ B)
--       have hbid : bid = Homeomorph.refl B := by
--         ext
--         exact e.toEquiv.apply_symm_apply _
--       sorry

#check Homeomorph.trans

variable (R)

lemma continuous_neg (A : Type*) [AddCommGroup A] [Module R A] [TopologicalSpace A]
    [IsModuleTopology R A] :
    Continuous (-· : A → A) :=
  continuous_of_linearMap (LinearMap.neg R A)

end function

section surj

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]

lemma surj {n : ℕ} {φ : ((Fin n) → R) →ₗ[R] A} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ Pi.topologicalSpace = moduleTopology R A := by
  apply le_antisymm
  · rw [← continuous_iff_coinduced_le, ← isModuleTopology R A]
    exact continuous_of_linearMap φ
  · apply iSup_le fun m ↦ iSup_le fun ψ ↦ ?_
    obtain ⟨α, rfl⟩ : ∃ α : (Fin m → R) →ₗ[R] (Fin n → R), φ.comp α = ψ :=
      Module.projective_lifting_property _ _ hφ
    push_cast
    rw [← coinduced_compose]
    apply coinduced_mono
    rw [← continuous_iff_coinduced_le]
    exact continuous_of_linearMap α

/-- Any surjection between finite R-modules is coinducing for the R-module topology. -/
lemma supersurj {B : Type*} [AddCommMonoid B] [aB : TopologicalSpace B] [Module R B] [IsModuleTopology R B]
    [Module.Finite R A] {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ (moduleTopology R A) = moduleTopology R B := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R A
  rw [← surj <| show  Function.Surjective (φ ∘ₗ f) by aesop]
  push_cast
  rw [← coinduced_compose, surj hf]

-- nice spot to end a PR.

-- do I need this?
-- **^TODO** why didn't have/let linter warn me
lemma surj' {ι : Type*} [Finite ι] {φ : (ι → R) →ₗ[R] A} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ Pi.topologicalSpace = moduleTopology R A := by
  rw [(instPiFinite R ι).isModuleTopology']
  apply supersurj hφ

end surj

section add

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]

open TopologicalSpace in
-- **TODO** ask Yury how to golf
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

variable (R A) in
@[continuity, fun_prop]
lemma continuous_add [Module.Finite R A] : Continuous (fun ab ↦ ab.1 + ab.2 : A × A → A) := by
  rw [continuous_iff_coinduced_le, isModuleTopology R A]
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R A
  rw [← surj hf]
  intro U hU
  rw [isOpen_coinduced] at hU ⊢
  apply Continuous.isOpen_preimage
      (f := (fun rs ↦ rs.1 + rs.2 : (Fin n → R) × (Fin n → R) → (Fin n → R)))
      (by continuity) at hU
  rw [← coinduced_prod_eq_prod_coinduced f f hf hf]
  suffices key : (fun ab ↦ ab.1 + ab.2 : A × A → A) ⁻¹' U =
    ⇑(f.prodMap f).toAddMonoidHom '' ((fun rs ↦ rs.1 + rs.2) ⁻¹' (⇑f ⁻¹' U)) by
    convert isOpenMap_of_coinduced (f.prodMap f).toAddMonoidHom
      (by rw [continuous_iff_coinduced_le]; rfl) rfl _ hU
      (τB := TopologicalSpace.coinduced (f.prodMap f) instTopologicalSpaceProd)
  ext ⟨a, b⟩
  simp only [Set.mem_preimage, LinearMap.toAddMonoidHom_coe, Set.mem_image, map_add, Prod.exists,
    LinearMap.prodMap_apply, Prod.mk.injEq]
  refine ⟨fun h ↦ ?_, by aesop⟩
  obtain ⟨s, rfl⟩ := hf a
  obtain ⟨t, rfl⟩ := hf b
  use s, t, h

variable (R A) in
@[continuity, fun_prop]
lemma continuous_sum_finset (ι : Type*) [DecidableEq ι] (s : Finset ι) [Module.Finite R A] :
    Continuous (fun as ↦ ∑ i ∈ s, as i : (∀ (_ : ι), A) → A) := by
  induction s using Finset.induction
  · simp only [Finset.sum_empty]
    fun_prop
  · case insert j s has hc =>
    simp_rw [Finset.sum_insert has]
    suffices Continuous (fun as ↦ (as j, ∑ i ∈ s, as i): ((ι → A) → A × A)) from
      Continuous.comp (continuous_add R A) this
    fun_prop

attribute [local instance] Fintype.ofFinite

lemma continuous_sum_finite (ι : Type*) [Finite ι] [Module.Finite R A] :
    Continuous (fun as ↦ ∑ i, as i : (∀ (_ : ι), A) → A) := by
  classical
  exact continuous_sum_finset R A ι _

end add


section prod

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]

open TopologicalSpace in
instance prod [Module.Finite R A] [Module.Finite R B] :
    IsModuleTopology R (A × B) := by
  constructor
  apply le_antisymm
  · rw [← continuous_id_iff_le, show (id : A × B → A × B) =
      (fun abcd ↦ abcd.1 + abcd.2) ∘ (fun ab ↦ ((ab.1, 0),(0, ab.2))) by
      ext ⟨a, b⟩ <;> simp]
    apply @Continuous.comp (A × B) ((A × B) × (A × B)) (A × B) _ (_) (_)
    · apply @continuous_add R _ _ _ (A × B) _ _ (_) <| IsModuleTopology.mk (τA := _) rfl
    · convert @Continuous.prod_map (A × B) (A × B) A B (moduleTopology R _) (moduleTopology R _)
          _ _ (LinearMap.inl R A B) (LinearMap.inr R A B) _ _ using 1
      · rw [isModuleTopology R A]
        apply continuous_of_linearMap'
      · rw [isModuleTopology R B]
        apply continuous_of_linearMap'
  · rw [isModuleTopology R A, isModuleTopology R B]
    apply le_inf <;> rw [← continuous_iff_le_induced]
    · exact continuous_of_linearMap' (LinearMap.fst R A B)
    · exact continuous_of_linearMap' (LinearMap.snd R A B)

end prod

section Pi

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]

variable {ι : Type*} {A : ι → Type*} [Finite ι] [∀ i, AddCommGroup (A i)]
    [∀ i, Module R (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsModuleTopology R (A i)]

lemma pi [∀ i, Module.Finite R (A i)]: IsModuleTopology R (∀ i, A i) := by
  constructor
  apply le_antisymm
  · rw [← continuous_id_iff_le]
    classical
    letI : Fintype ι := Fintype.ofFinite ι
    have hid : id = (fun l ↦ ∑ j, l j : (∀ (_ : ι), ∀ i, A i) → ∀ i, A i) ∘
        (fun as ↦ (fun j ↦ (fun i ↦ if h : i = j then h ▸ as j else 0))) := by
      ext
      simp
    rw [hid]
    apply @Continuous.comp _ _ _ _ (_) (_)
    · apply @continuous_sum_finite R _ _ _ _ _ _ (moduleTopology R _) ?_
      convert IsModuleTopology.mk rfl
    · refine @Pi.continuous_postcomp' _ _ _ _ (fun _ ↦ moduleTopology R (∀ i, A i))
          (fun j aj k ↦ if h : k = j then h ▸ aj else 0) (fun i ↦ ?_)
      rw [isModuleTopology R (A i)]
      exact continuous_of_linearMap' (LinearMap.single i)
  · apply le_iInf (fun i ↦ ?_)
    rw [← continuous_iff_le_induced, isModuleTopology R (A i)]
    exact continuous_of_linearMap' (LinearMap.proj i)


-- lemma pi' [∀ i, Module.Finite R (A i)]: IsModuleTopology R (∀ i, A i) := by
--   induction ι using Finite.induction_empty_option with
--   | of_equiv e => sorry
--   | h_empty => sorry
--   | h_option => sorry

end Pi

section commutative

open scoped TensorProduct

variable {R : Type*} [τR : TopologicalSpace R] [CommRing R] [TopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable [aAB : TopologicalSpace (A ⊗[R] B)] [IsModuleTopology R (A ⊗[R] B)]

noncomputable def isom'' (R : Type*) [CommRing R] (m n : Type*) [Finite m] [DecidableEq m] :
    (m → R) ⊗[R] (n → R) ≃ₗ[R] (m × n → R) := sorry -- done in mathlib

variable (m n : Type*) [Finite m] [Finite n] [DecidableEq m] [DecidableEq n] (a1 : m → R)
    (b1 : n → R) (f : (m → R) →ₗ[R] A) (g : (n → R) →ₗ[R] B) in
lemma key : ((TensorProduct.map f g ∘ₗ
    (isom'' R m n).symm.toLinearMap) fun mn ↦ a1 mn.1 * b1 mn.2) = f a1 ⊗ₜ[R] g b1 := by
  sorry

-- once mathlib#16122 is merged we can bump and then replace `isom''` with
-- `finiteTensorPiLid R R m n` and `key` with the following: (M ↦ A, N ↦ B)
-- and this should complete the proof.

-- variable (m n : Type*) [Finite m] [DecidableEq m] (a1 : m → R)
--     (b1 : n → R) (f : (m → R) →ₗ[R] M) (g : (n → R) →ₗ[R] N) in
-- example : ((TensorProduct.map f g ∘ₗ (finiteTensorPiLid R R m n).symm.toLinearMap)
--   fun mn ↦ a1 mn.1 * b1 mn.2) = f a1 ⊗ₜ[R] g b1 := by
--   refine congr_arg (map f g) ((Equiv.symm_apply_eq (finiteTensorPiLid R R m n).toEquiv).2 ?_ :
--     (finiteTensorPiLid R R m n).symm.toLinearMap (fun mn ↦ a1 mn.1 * b1 mn.2) = a1 ⊗ₜ b1)
--   ext ⟨m, n⟩
--   simp


-- I don't know whether finiteness is needed on `B` here. Removing it here would enable
-- removal in `continuous_bilinear`.
@[continuity, fun_prop]
lemma Module.continuous_tprod [Module.Finite R A] [Module.Finite R B] :
    Continuous (fun (ab : A × B) ↦ ab.1 ⊗ₜ ab.2 : A × B → A ⊗[R] B) := by
  -- reduce to R^m x R^n -> R^m ⊗ R^n
  -- then check explicitly
  rw [continuous_iff_coinduced_le, isModuleTopology R A, isModuleTopology R B, isModuleTopology R (A ⊗[R] B)]
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R A
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R B
  have hψ := TensorProduct.map_surjective hf hg
  let φ : (Fin m × Fin n → R) →ₗ[R] A ⊗[R] B :=
    (TensorProduct.map f g) ∘ₗ (isom'' R (Fin m) (Fin n)).symm.toLinearMap
  have hφ : Function.Surjective φ := by aesop
  rw [← surj' hφ]
  intro U hU
  -- hU says that U is open for the action topology on A ⊗ B
  rw [isOpen_coinduced] at hU ⊢
  apply @Continuous.isOpen_preimage ((Fin m → R) × (Fin n → R)) ((Fin m × Fin n) → R) _ _
      (fun rs mn ↦ rs.1 mn.1 * rs.2 mn.2) (by fun_prop) at hU
  let α : (Fin m → R) × (Fin n → R) →ₗ[R] A × B := f.prodMap g
  convert isOpenMap_of_coinduced (τB := TopologicalSpace.coinduced α instTopologicalSpaceProd)
    α.toAddMonoidHom _ rfl _ hU
  · convert (rfl : moduleTopology R (A × B) = moduleTopology R (A × B))
    ·
      suffices IsModuleTopology R (A × B) by
        convert this.isModuleTopology'
        · symm
          apply isModuleTopology
        · symm
          apply isModuleTopology
      exact prod
    · have hα : Function.Surjective α := by
        unfold_let
        -- missing API Function.prodmapsurjective
        rintro ⟨a, b⟩
        obtain ⟨x, rfl⟩ := hf a
        obtain ⟨y, rfl⟩ := hg b
        use (x, y)
        rfl
      convert supersurj hα
      exact isModuleTopology R _
    -- looks fine
  · ext x
    obtain ⟨a, b⟩ := x
    simp [α]
    -- need def of isom''
    constructor
    · intro h
      obtain ⟨a1, rfl⟩ := hf a
      obtain ⟨b1, rfl⟩ := hg b
      use a1, b1, ?_, rfl
      /-
      case left
      φ : (Fin m × Fin n → R) →ₗ[R] A ⊗[R] B := TensorProduct.map f g ∘ₗ ↑isom''.symm
      hφ : Function.Surjective ⇑φ
      a1 : Fin m → R
      b1 : Fin n → R
      h : f a1 ⊗ₜ[R] g b1 ∈ U
      ⊢ (φ fun mn ↦ a1 mn.1 * b1 mn.2) ∈ U
      -/
      unfold_let
      rwa [key]
    · rintro ⟨a1, b1, hU, rfl, rfl⟩
      rwa [← key]
  · rw [continuous_iff_coinduced_le]
    rfl

-- did I really use finiteness of B?
lemma Module.continuous_bilinear [Module.Finite R A] [Module.Finite R B]
    {C : Type*} [AddCommGroup C] [Module R C] [TopologicalSpace C] [IsModuleTopology R C]
    (bil : A →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  letI : TopologicalSpace (A ⊗[R] B) := moduleTopology R _
  haveI : IsModuleTopology R (A ⊗[R] B) := ⟨rfl⟩
  change Continuous (TensorProduct.uncurry R A B C bil ∘ (fun (ab : A × B) ↦ ab.1 ⊗ₜ ab.2))
  fun_prop
  -- `fun_prop` unravels to
  -- -- set_option pp.explicit true in
  -- -- set_option pp.instances false in
  -- exact
  --   @Continuous.comp' (Prod A B) (@TensorProduct R _ A B _ _ _ _) C _ _ _
  --     (fun a ↦ (fun ab ↦ @TensorProduct.tmul R _ A B _ _ _ _ ab.1 ab.2) a)
  --     (fun a12 ↦ ((@TensorProduct.uncurry R _ A B C _ _ _ _ _ _) bil) a12)
  --     (@continuous_of_linearMap R _ _ (@TensorProduct R _ A B _ _ _ _) _ _ _ _ C _ _ _ _
  --       ((@TensorProduct.uncurry R _ A B C _ _ _ _ _ _) bil))
  --     (@continuous_tprod R _ _ _ A _ _ _ _ B _ _ _ _ _ _ _ _)

variable (R)
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

@[continuity, fun_prop]
lemma continuous_mul : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) := by
  letI : TopologicalSpace (D ⊗[R] D) := moduleTopology R _
  haveI : IsModuleTopology R (D ⊗[R] D) := { isModuleTopology' := rfl }
  apply Module.continuous_bilinear <| LinearMap.mul R D

def Module.topologicalRing : TopologicalRing D :=
  {
    continuous_add := continuous_add R D
    continuous_mul := continuous_mul R D
    continuous_neg := continuous_neg R D}

end commutative

lemma continuousSMul (R : Type*) [CommRing R] [TopologicalSpace R] [TopologicalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] [TopologicalSpace A]
    [IsModuleTopology R A] :
    ContinuousSMul R A := by
  exact ⟨Module.continuous_bilinear <| LinearMap.lsmul R A⟩

end ModuleTopology

/-

## Open problem

I can only prove that `SMul : R × A → A` is continuous for the module topology if `R` is
commutative (because my proof uses tensor products) and if `A` is finite (because
I reduce to a basis check ). Is it true in general?

lemma continuousSMul (R : Type*) [Ring R] [TopologicalSpace R] [TopologicalRing R]
    (A : Type*) [AddCommGroup A] [Module R A] : @ContinuousSMul R A _ _ (moduleTopology R A) := by
  refine @ContinuousSMul.mk ?_ ?_ ?_ ?_ ?_ ?_
  haveI : IsModuleTopology R R := inferInstance
  rw [isModuleTopology R R]
  refine Module.continuous_bilinear ?_
  sorry
-/
