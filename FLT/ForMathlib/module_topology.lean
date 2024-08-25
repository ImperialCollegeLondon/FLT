import Mathlib.RingTheory.TensorProduct.Basic -- we need tensor products of rings at some point
import Mathlib.Topology.Algebra.Module.Basic -- and we need topological rings and modules
import Mathlib.Tactic
import Mathlib.Topology.Order
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-
# An topology for monoid actions.

If `R` is a topological ring and `A` is an `R`-module, then there are several ways in which
`A` can inherit a topology from `R` via the action. We make one such definiion here,
which we call the *module* topology, or the `R`-module topology if there is an ambiguity.
This topology has very nice properties on the category of finite R-modules. For example,
all `R`-linear maps between finite `A`-modules are continuous, and given any `R`-linear surjection
`Rⁿ → A` for `n` finite, the topology on `A` is the pushforward of the product topology on `Rⁿ`.
This has importance in the theory of algebraic groups over local fields such as the reals
or the `p`-adics. Example: if `A` is a finite-dimensional central simple algebra over a
topological ring `R`, then in the representation theory of algebraic groups we would like
to consider certain continuous representations of `Aˣ`, so `A` needs a topology. In our
approach we can do the following:

-/

-- section continuous_smul

-- variable {R : Type} [τR : TopologicalSpace R]
-- variable {A : Type} [SMul R A]
-- variable {S : Type} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)
-- variable {B : Type} [SMul S B] (g : B →ₑ[f] A)

-- -- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B
-- lemma induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] :
--     @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
--   convert Inducing.continuousSMul (inducing_induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

-- #check Prod.continuousSMul -- exists and is an instance :-)
-- --#check Induced.continuousSMul -- doesn't exist

-- end continuous_smul

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

end elsewhere

section basics

variable (R : Type*) [TopologicalSpace R] [Ring R] [TopologicalRing R]
variable (A : Type*) [AddCommMonoid A] [Module R A]

-- "smallest" (i.e. most open sets) topology on `A` such
-- that all R-linear maps R^n → A are continuous
abbrev actionTopology : TopologicalSpace A :=
  ⨆ (n : ℕ), ⨆ (φ : (Fin n → R) →ₗ[R] A), .coinduced φ inferInstance

class IsActionTopology [τA : TopologicalSpace A] : Prop where
  isActionTopology' : τA = actionTopology R A

-- because default binders for isActionTopology' are wrong and currently
-- there is no way to change this. See lean4#...**TODO**
lemma isActionTopology [τA : TopologicalSpace A] [IsActionTopology R A] :
    τA = actionTopology R A :=
  IsActionTopology.isActionTopology' (R := R) (A := A)

-- **TODO** is this true?
-- lemma ActionTopology.continuousSMul : @ContinuousSMul R A _ _ (actionTopology R A) :=
--   continuousSMul_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

-- **TODO** follows from the above
-- instance isActionTopology_continuousSMul (R A : Type*) [SMul R A]
--     [TopologicalSpace R] [τA : TopologicalSpace A] [h : IsActionTopology R A] :
--   ContinuousSMul R A where
--     continuous_smul := by
--       obtain ⟨h⟩ := ActionTopology.continuousSMul R A
--       simpa [isActionTopology R A] using h

end basics

namespace ActionTopology

section one

variable (R : Type*) [Ring R] [τ : TopologicalSpace R] [TopologicalRing R]

protected lemma id : IsActionTopology R R := by
  constructor
  apply le_antisymm
  · refine le_iSup_of_le 1 ?_
    refine le_iSup_of_le (LinearMap.proj 0) (fun U hU ↦ ?_)
    rw [isOpen_coinduced] at hU
    exact Continuous.isOpen_preimage (f := fun r ↦ (fun _ ↦ r)) (by fun_prop) _ hU
  · apply iSup_le
    intro n
    apply iSup_le
    intro φ
    rw [← continuous_iff_coinduced_le]
    exact LinearMap.continuous_on_pi φ

instance pow (n : ℕ) : IsActionTopology R (Fin n → R) := by
  constructor
  apply le_antisymm
  · refine le_iSup_of_le n ?_
    refine le_iSup_of_le (LinearMap.id) ?_
    intro U hU
    rw [isOpen_coinduced] at hU
    apply hU
  · apply iSup_le
    intro m
    apply iSup_le
    intro φ
    rw [← continuous_iff_coinduced_le]
    exact LinearMap.continuous_on_pi φ

end one

section function

variable {R : Type*} [τR : TopologicalSpace R] [Ring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

variable {C : Type*} [AddCommGroup C] [Module R C]

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
@[continuity, fun_prop]
lemma continuous_of_linearMap (f : A →ₗ[R] B) : Continuous f := by
  rw [isActionTopology R A, continuous_iff_le_induced]
  apply iSup_le <| fun n ↦ ?_
  apply iSup_le <| fun φ ↦ ?_
  rw [isActionTopology R B, ← coinduced_le_iff_le_induced, coinduced_compose]
  apply le_iSup_of_le n
  apply le_iSup_of_le (f.comp φ)
  rfl

lemma continuous_of_linearMap' {A : Type*} [AddCommMonoid A] [Module R A]
    {B : Type*} [AddCommMonoid B] [Module R B] (f : A →ₗ[R] B) :
    @Continuous _ _ (actionTopology R A) (actionTopology R B) f := by
  letI : TopologicalSpace A := actionTopology R A
  letI : TopologicalSpace B := actionTopology R B
  haveI : IsActionTopology R A := ⟨rfl⟩
  haveI : IsActionTopology R B := ⟨rfl⟩
  fun_prop

variable (R)
def _root_.LinearMap.neg (A : Type*) [AddCommGroup A] [Module R A] : A →ₗ[R] A where
  toFun := (-·)
  map_add' := neg_add
  map_smul' r a := (smul_neg r a).symm

lemma continuous_neg (A : Type*) [AddCommGroup A] [Module R A] [TopologicalSpace A]
    [IsActionTopology R A] :
    Continuous (-· : A → A) :=
  continuous_of_linearMap (LinearMap.neg R A)

end function

section surj

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]

lemma surj {n : ℕ} {φ : ((Fin n) → R) →ₗ[R] A} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ Pi.topologicalSpace = actionTopology R A := by
  apply le_antisymm
  · rw [← continuous_iff_coinduced_le]
    rw [← isActionTopology R A]
    fun_prop
  · rw [iSup_le_iff]
    intro m
    rw [iSup_le_iff]
    intro ψ
    obtain ⟨α, rfl⟩ : ∃ α : (Fin m → R) →ₗ[R] (Fin n → R), φ.comp α = ψ :=
      Module.projective_lifting_property _ _ hφ
    change TopologicalSpace.coinduced (φ ∘ α) _ ≤ _
    rw [← coinduced_compose]
    apply coinduced_mono
    rw [← continuous_iff_coinduced_le]
    fun_prop

lemma supersurj {B : Type*} [AddCommMonoid B] [aB : TopologicalSpace B] [Module R B] [IsActionTopology R B]
    [Module.Finite R A] {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ (actionTopology R A) = actionTopology R B := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R A
  have hg : Function.Surjective (φ ∘ₗ f) := by aesop
  rw [← surj hg]
  convert coinduced_compose
  convert (surj hf).symm

-- **^TODO** why didn't have/let linter warn me
lemma surj' {ι : Type*} [Finite ι] {φ : (ι → R) →ₗ[R] A} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ Pi.topologicalSpace = actionTopology R A := by
  let n := Nat.card ι
  let f : (Fin n → R) ≃ₗ[R] (ι → R) := LinearEquiv.funCongrLeft R R (Finite.equivFin ι)
  have hf : Function.Surjective (φ ∘ₗ f : (Fin n → R) →ₗ[R] A) := by simp [hφ]
  rw [← surj hf]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, ← coinduced_compose, f]
  congr
  let foo' : (ι → R) ≃ₜ (Fin (Nat.card ι) → R) :=
    Homeomorph.piCongrLeft (Y := fun _ ↦ R) (Finite.equivFin ι)
  exact (Homeomorph.coinduced_eq foo'.symm).symm

end surj

section add

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]

example : A × A →ₗ[R] A := LinearMap.fst R A A + LinearMap.snd R A A

open TopologicalSpace in
-- **TODO** ask Yury how to golf
lemma coinduced_prod_eq_prod_coinduced (X Y S T : Type*) [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup S] [AddCommGroup T] (f : X →+ S) (g : Y →+ T)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [τX : TopologicalSpace X] [ContinuousAdd X] [τY : TopologicalSpace Y] [ContinuousAdd Y] :
    coinduced (Prod.map f g) instTopologicalSpaceProd =
      @instTopologicalSpaceProd S T (coinduced f τX) (coinduced g τY) := by
  ext U
  rw [@isOpen_prod_iff]
  rw [isOpen_coinduced]
  rw [isOpen_prod_iff]
  constructor
  · intro h s t hst
    obtain ⟨x, rfl⟩ := hf s
    obtain ⟨y, rfl⟩ := hg t
    obtain ⟨V1, V2, hV1, hV2, hx1, hy2, h12⟩ := h x y hst
    have this1 := @isOpenMap_of_coinduced _ _ _ _ _ _ (coinduced f τX) f ?_ rfl V1 hV1
    · have this2 := @isOpenMap_of_coinduced _ _ _ _ _ _ (coinduced g τY) g ?_ rfl V2 hV2
      · use f '' V1, g '' V2, this1, this2, ⟨x, hx1, rfl⟩, ⟨y, hy2, rfl⟩
        intro ⟨s, t⟩ ⟨⟨x', hx', hxs⟩, ⟨y', hy', hyt⟩⟩
        subst hxs hyt
        specialize @h12 (x', y') ⟨hx', hy'⟩
        exact h12
      · rw [continuous_iff_coinduced_le]
    · rw [continuous_iff_coinduced_le]
  · intro h x y hxy
    rw [Set.mem_preimage, Prod.map_apply] at hxy
    obtain ⟨U1, U2, hU1, hU2, hx1, hy2, h12⟩ := h (f x) (g y) hxy
    use f ⁻¹' U1, g ⁻¹' U2, hU1, hU2, hx1, hy2
    intro ⟨x', y'⟩ ⟨hx', hy'⟩
    apply h12
    exact ⟨hx', hy'⟩

variable (R A) in
@[continuity, fun_prop]
lemma continuous_add [Module.Finite R A] : Continuous (fun ab ↦ ab.1 + ab.2 : A × A → A) := by
  rw [continuous_iff_coinduced_le, isActionTopology R A]
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R A
  rw [← surj hf]
  intro U hU
  rw [isOpen_coinduced] at hU ⊢
  apply @Continuous.isOpen_preimage ((Fin n → R) × (Fin n → R)) (Fin n → R) _ _
      (fun rs ↦ rs.1 + rs.2) (by continuity) at hU
  let ff : (Fin n → R) × (Fin n → R) →ₗ[R] A × A := f.prodMap f
  convert isOpenMap_of_coinduced (τB := TopologicalSpace.coinduced ff instTopologicalSpaceProd)
    ff.toAddMonoidHom _ rfl _ hU
  · convert (coinduced_prod_eq_prod_coinduced _ _ A A f f hf hf).symm
  · ext x
    cases' x with a b
    simp only [Set.mem_preimage, LinearMap.toAddMonoidHom_coe, Set.mem_image, map_add, Prod.exists]
    constructor
    · intro h
      obtain ⟨a1, rfl⟩ := hf a
      obtain ⟨b1, rfl⟩ := hf b
      use a1, b1, h
      rfl
    · rintro ⟨a1, b1, hU, hab⟩
      cases hab
      exact hU
  · rw [continuous_iff_coinduced_le]
    rfl

variable (R A) in
@[continuity, fun_prop]
lemma continuous_sum_finset (ι : Type*) [DecidableEq ι] (s : Finset ι) [Module.Finite R A] :
    Continuous (fun as ↦ ∑ i ∈ s, as i : (∀ (_ : ι), A) → A) := by
  induction s using Finset.induction
  · simp only [Finset.sum_empty]
    fun_prop
  · case insert j s has hc =>
    simp_rw [Finset.sum_insert has]
    have foo : (fun (as : ∀ _, A) ↦ as j + ∑ i ∈ s, as i) = (fun ab ↦ ab.1 + ab.2 : A × A → A) ∘
        (fun as ↦ (as j, ∑ i ∈ s, as i) : ((∀ _, A) → A × A)) := by
      ext
      simp
    rw [foo]
    apply Continuous.comp
    · apply continuous_add R A
    · fun_prop

attribute [local instance] Fintype.ofFinite

lemma continuous_sum_finite (ι : Type*) [Finite ι] [Module.Finite R A] :
    Continuous (fun as ↦ ∑ i, as i : (∀ (_ : ι), A) → A) := by
  classical
  exact continuous_sum_finset R A ι _

end add


section prod

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

open TopologicalSpace in
lemma prod [Module.Finite R A] [Module.Finite R B] :
    IsActionTopology R (A × B) := by
  constructor
  apply le_antisymm
  · rw [← continuous_id_iff_le]
    have hid : @id (A × B) = (fun abcd ↦ abcd.1 + abcd.2) ∘ (fun ab ↦ ((ab.1, 0),(0, ab.2))) := by
      ext ⟨a, b⟩ <;> simp
    rw [hid]
    apply @Continuous.comp (A × B) ((A × B) × (A × B)) (A × B) _
        (@instTopologicalSpaceProd _ _ (actionTopology R _) (actionTopology R _))
        (actionTopology R _) _ _
    · apply @continuous_add R _ _ _ (A × B) _ _ (actionTopology R _) ?_
      convert IsActionTopology.mk rfl
    · convert @Continuous.prod_map (A × B) (A × B) A B (actionTopology R _) (actionTopology R _)
          _ _ (LinearMap.inl R A B) (LinearMap.inr R A B) _ _ using 1
      · rw [isActionTopology R A]
        apply continuous_of_linearMap'
      · rw [isActionTopology R B]
        apply continuous_of_linearMap'
  · apply le_inf
    · rw [← continuous_iff_le_induced]
      rw [isActionTopology R A]
      change @Continuous (A × B) A (actionTopology R _) (actionTopology R _) (LinearMap.fst R A B)
      apply continuous_of_linearMap'
    · rw [← continuous_iff_le_induced]
      rw [isActionTopology R B]
      change @Continuous (A × B) B (actionTopology R _) (actionTopology R _) (LinearMap.snd R A B)
      apply continuous_of_linearMap'

variable (R A B) in
lemma prod_isActionTopology [Module.Finite R A] [Module.Finite R B] :
    (instTopologicalSpaceProd : TopologicalSpace (A × B)) = actionTopology R (A × B) := by
  convert prod.isActionTopology' <;> all_goals infer_instance

end prod

section Pi

variable {R : Type} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]

variable {ι : Type} {A : ι → Type} [Finite ι] [∀ i, AddCommGroup (A i)]
    [∀ i, Module R (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsActionTopology R (A i)]

lemma pi [∀ i, Module.Finite R (A i)]: IsActionTopology R (∀ i, A i) := by
  constructor
  apply le_antisymm
  · rw [← continuous_id_iff_le]
    classical
    letI : Fintype ι := Fintype.ofFinite ι
    have hid : @id (∀ i, A i) = (fun l ↦ ∑ j, l j : (∀ (_ : ι), ∀ i, A i) → ∀ i, A i) ∘
        (fun as ↦ (fun j ↦ (fun i ↦ if h : i = j then h ▸ as j else 0))) := by
      ext
      simp
    rw [hid]
    apply @Continuous.comp _ _ _ _ (@Pi.topologicalSpace ι _ (fun i ↦ actionTopology R _))
        (actionTopology R _) _ _
    · apply @continuous_sum_finite R _ _ _ _ _ _ (actionTopology R _) ?_
      convert IsActionTopology.mk rfl
    · refine @Pi.continuous_postcomp' _ _ _ _ (fun _ ↦ actionTopology R (∀ i, A i))
          (fun j aj k ↦ if h : k = j then h ▸ aj else 0) (fun i ↦ ?_)
      rw [isActionTopology R (A i)]
      exact continuous_of_linearMap' (LinearMap.single i)
  · apply le_iInf (fun i ↦ ?_)
    rw [← continuous_iff_le_induced, isActionTopology R (A i)]
    exact continuous_of_linearMap' (LinearMap.proj i)

end Pi

section commutative

open scoped TensorProduct

variable {R : Type*} [τR : TopologicalSpace R] [CommRing R] [TopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]
variable [aAB : TopologicalSpace (A ⊗[R] B)] [IsActionTopology R (A ⊗[R] B)]

noncomputable def isom'' (R : Type*) [CommRing R] (m n : Type*) [Finite m] [DecidableEq m] :
    (m → R) ⊗[R] (n → R) ≃ₗ[R] (m × n → R) := sorry -- done in mathlib

variable (m n : Type*) [Finite m] [Finite n] [DecidableEq m] [DecidableEq n] (a1 : m → R)
    (b1 : n → R) (f : (m → R) →ₗ[R] A) (g : (n → R) →ₗ[R] B) in
lemma key : ((TensorProduct.map f g ∘ₗ
    (isom'' R m n).symm.toLinearMap) fun mn ↦ a1 mn.1 * b1 mn.2) = f a1 ⊗ₜ[R] g b1 := by
  sorry

-- once we have mathlib#16122 we can replace `isom''` with `finiteTensorPiLid R R m n`
-- and `key` with the following: (M ↦ A, N ↦ B)

-- variable (m n : Type*) [Finite m] [DecidableEq m] (a1 : m → R)
--     (b1 : n → R) (f : (m → R) →ₗ[R] M) (g : (n → R) →ₗ[R] N) in
-- example : ((TensorProduct.map f g ∘ₗ (finiteTensorPiLid R R m n).symm.toLinearMap)
--   fun mn ↦ a1 mn.1 * b1 mn.2) = f a1 ⊗ₜ[R] g b1 := by
--   refine congr_arg (map f g) ((Equiv.symm_apply_eq (finiteTensorPiLid R R m n).toEquiv).2 ?_ :
--     (finiteTensorPiLid R R m n).symm.toLinearMap (fun mn ↦ a1 mn.1 * b1 mn.2) = a1 ⊗ₜ b1)
--   ext ⟨m, n⟩
--   simp

@[continuity, fun_prop]
lemma Module.continuous_tprod [Module.Finite R A] [Module.Finite R B] :
    Continuous (fun (ab : A × B) ↦ ab.1 ⊗ₜ ab.2 : A × B → A ⊗[R] B) := by
  -- reduce to R^m x R^n -> R^m ⊗ R^n
  -- then check explicitly
  rw [continuous_iff_coinduced_le, isActionTopology R A, isActionTopology R B, isActionTopology R (A ⊗[R] B)]
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
  · convert (rfl : actionTopology R (A × B) = actionTopology R (A × B))
    ·
      suffices IsActionTopology R (A × B) by
        convert this.isActionTopology'
        · symm
          apply isActionTopology
        · symm
          apply isActionTopology
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
      · exact prod_isActionTopology R (Fin m → R) (Fin n → R)
      · apply prod
      · apply prod
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

lemma Module.continuous_bilinear [Module.Finite R A] [Module.Finite R B]
    {C : Type*} [AddCommGroup C] [Module R C] [TopologicalSpace C] [IsActionTopology R C]
    (bil : A →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  change Continuous (TensorProduct.uncurry R A B C bil ∘ (fun (ab : A × B) ↦ ab.1 ⊗ₜ ab.2))
  fun_prop

variable (R)
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsActionTopology R D]

@[continuity, fun_prop]
lemma continuous_mul : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) := by
  letI : TopologicalSpace (D ⊗[R] D) := actionTopology R _
  haveI : IsActionTopology R (D ⊗[R] D) := { isActionTopology' := rfl }
  apply Module.continuous_bilinear <| LinearMap.mul R D

def Module.topologicalRing : TopologicalRing D :=
  {
    continuous_add := continuous_add R D
    continuous_mul := continuous_mul R D
    continuous_neg := continuous_neg R D}

end commutative

end ActionTopology
