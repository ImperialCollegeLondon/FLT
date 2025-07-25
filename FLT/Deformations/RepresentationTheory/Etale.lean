import Mathlib.FieldTheory.Galois.Infinite
import FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Equivalence between continuous `G`-finite sets and `k`-etale algebras

Given a group `G`, fields `L/K` with `L` separably closed,
such that `G` acts on `L` by `K`-algebra homomorphisms.
We have a contravariant adjunction
`G`-set ↔ `K`-algebra
`X → Hom_G(X, L)`,
`Hom_K(A, L) ← A`
with unit and counits:
`AlgHom.evalMulActionHom`: `A →ₐ[K] ((A →ₐ[K] L) →[G] L)`
`MulActionHom.evalAlgHom`: `X →[G] ((X →[G] L) →ₐ[K] L)`

Suppose `L/K` is galois with galois group `G`:

* If `X` is finite discrete with continuous `G` action, then `X →[G] L` is finite etale.

* `InfiniteGalois.evalAlgHom_bijective`:
  If `X` is finite discrete with continuous `G` action, then `MulActionHom.evalAlgHom` is bijective.

* If `A/K` is finite dimensional then `A →ₐ[K] L` is finite discrete with continuous `G` action.

* `InfiniteGalois.evalMulActionHom_bijective`:
  If `A/K` is etale, and `L` contains all residue fields of `A` (in particular when
  `L` is separably closed), then `AlgHom.evalMulActionHom` is bijective.

Taking `L = Kˢᵉᵖ`, the adjunction restricts to a (contravariant) equivalence
between finite discrete `Gₖ`-sets and finite etale `k`-algebras.

-/

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable (X : Type u) [MulAction (L ≃ₐ[K] L) X]

instance {G H X Y : Type*} [Monoid G] [MulAction G X] [MulAction G Y]
    [SMul H Y] [SMulCommClass G H Y] :
    SMul H (X →[G] Y) where
  smul h f := ⟨h • f, by simp [smul_comm _ h]⟩

instance {G H X Y : Type*} [Monoid G] [MulAction G X] [Semiring Y] [MulSemiringAction G Y]
    [CommSemiring H] [Algebra H Y] [SMulCommClass G H Y] :
    Algebra H (X →[G] Y) where
  algebraMap :=
  { toFun h := ⟨fun _ ↦ algebraMap H Y h, by simp⟩
    map_one' := by ext; simp; rfl
    map_mul' _ _ := by ext; simp; rfl
    map_zero' := by ext; simp; rfl
    map_add' _ _ := by ext; simp; rfl }
  commutes' _ _ := MulActionHom.ext fun _ ↦ Algebra.commutes _ _
  smul_def' _ _ := MulActionHom.ext fun _ ↦ Algebra.smul_def _ _

open TensorProduct

/-- Composing `MulActionHom` on the left as an `AlgHom`. -/
def MulActionHom.compLeftAlgHom (G R Y : Type*) {X X' : Type*}
    [Monoid G] [MulAction G X] [MulAction G X'] [Semiring Y] [MulSemiringAction G Y]
    [CommSemiring R] [Algebra R Y] [SMulCommClass G R Y] (f : X →[G] X') :
    (X' →[G] Y) →ₐ[R] (X →[G] Y) where
  toFun := (·.comp f)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The coercion from `MulActionHom` to functions as an `AlgHom`. -/
def MulActionHom.toFunAlgHom
    {G H X Y : Type*} [Monoid G] [MulAction G X] [Semiring Y] [MulSemiringAction G Y]
    [CommSemiring H] [Algebra H Y] [SMulCommClass G H Y] :
    (X →[G] Y) →ₐ[H] (X → Y) where
  toFun f := f
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
lemma MulAction.orbitRel.Quotient.mk_smul {G X : Type*} [Group G] [MulAction G X] (g : G) (x : X) :
  (⟦g • x⟧ : orbitRel.Quotient G X) = ⟦x⟧ := Quotient.sound ⟨g, rfl⟩

/-- Given a representative for each orbit of `X` under `G`, and for each `x : X` a choice of `σ`
that sends `x` to the representative, we obtain a bijection between `G`-equivariant homs from `X`
and the product of `Stab(x)`-fixed points over each orbit representative `x`. -/
@[simps]
def MulAction.homEquivProdFixedPoints {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (σ : X → G) (hσ : ∀ a b, orbitRel G X a b → σ a • a = σ b • b) :
    (X →[G] Y) ≃ Π i : Set.range (fun i ↦ σ i • i), fixedPoints (stabilizer G i.1) Y where
  toFun f i := ⟨f i, fun ⟨σ, hσ⟩ ↦ by simp [← map_smul, show _ = _ from hσ]⟩
  invFun v := ⟨fun x ↦ (σ x)⁻¹ • v ⟨_, x, rfl⟩, by
    intro τ x
    rw [inv_smul_eq_iff]
    trans (v ⟨_, x, rfl⟩).1
    · congr 2 <;> simp [hσ (τ • x) x ⟨τ, rfl⟩]
    simp only [← mul_smul]
    refine ((v ⟨_, x, rfl⟩).2 ⟨_ * _, ?_⟩).symm
    simp [mul_smul, hσ (τ • x) x ⟨τ, rfl⟩]⟩
  left_inv f := by ext; simp; rfl
  right_inv v := by
    ext x
    have : σ x.1 • x.1 = x.1 := by obtain ⟨_, x, rfl⟩ := x; exact hσ _ _ ⟨σ x, rfl⟩
    refine inv_smul_eq_iff.mpr (.trans ?_ ((v x).2 ⟨_, this⟩).symm)
    congr 2 <;> simp [this]

open IntermediateField in
/-- Given a representative for each orbit of `X` under `G := Gal(L/K)`,
and for each `x : X` a choice of `σ` that sends `x` to the representative,
we obtain a `K`-algebra isomorphism between `G`-equivariant homs from `X`
and the product of `Stab(x)`-fixed points over each orbit representative `x`. -/
def MulAction.etaleSubalgebraEquiv
    (σ : X → L ≃ₐ[K] L) (hσ : ∀ a b, orbitRel (L ≃ₐ[K] L) X a b → σ a • a = σ b • b) :
    (X →[L ≃ₐ[K] L] L) ≃ₐ[K]
      Π i : Set.range (fun i ↦ σ i • i), fixedField (stabilizer (L ≃ₐ[K] L) i.1) where
  __ := MulAction.homEquivProdFixedPoints σ hσ
  map_mul' f g := by ext i; rfl
  map_add' f g := by ext i; rfl
  commutes' k := by ext i; rfl

lemma RingHom.exists_map_single_ne_zero
    {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [Nontrivial S] (f : (Π i, R i) →+* S) :
    ∃ i, f (Pi.single i 1) ≠ 0 := by
  cases nonempty_fintype ι
  by_contra! H
  simpa [H] using DFunLike.congr_arg f (Finset.univ_sum_single 1)

/-- Given a map from a product of rings to a nontrivial ring, this is an arbitrary index whose
corresponding component is not sent to zero. -/
noncomputable
def RingHom.piIndex {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [Nontrivial S] (f : (Π i, R i) →+* S) : ι :=
  f.exists_map_single_ne_zero.choose

lemma RingHom.single_piIndex_ne_zero {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [Nontrivial S] (f : (Π i, R i) →+* S) :
    f (Pi.single f.piIndex 1) ≠ 0 :=
  f.exists_map_single_ne_zero.choose_spec

@[simp]
lemma RingHom.single_piIndex_one {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [IsDomain S] (f : (Π i, R i) →+* S) :
    f (Pi.single f.piIndex 1) = 1 :=
  mul_left_injective₀ f.single_piIndex_ne_zero (by simp [← map_mul, ← Pi.single_mul])

@[simp]
lemma RingHom.single_piIndex {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [IsDomain S] (f : (Π i, R i) →+* S) (x : Π i, R i) :
    f (Pi.single f.piIndex (x _)) = f x := by
  conv_rhs => rw [← one_mul (f x), ← f.single_piIndex_one, ← f.map_mul]
  rw [← Pi.single_mul_left, one_mul]

/-- `Pi.single` as a `NonUnitalRingHom`. -/
noncomputable
def NonUnitalRingHom.single {ι : Type*} (R : ι → Type*) [DecidableEq ι]
    [∀ i, NonUnitalNonAssocSemiring (R i)] (i) : R i →ₙ+* Π i, R i where
  __ := AddMonoidHom.single R i
  map_mul' _ _ := Pi.single_mul _ _ _

@[simp]
lemma NonUnitalRingHom.single_apply {ι : Type*} {R : ι → Type*} [DecidableEq ι]
    [∀ i, NonUnitalNonAssocSemiring (R i)] (i : ι) (x : R i) : single R i x = Pi.single i x := rfl

@[simp]
lemma RingHom.toNonUnitalRingHom_apply {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) (x : R) : f.toNonUnitalRingHom x = f x := rfl

/-- A map from a product of rings to a domain must factor through one of the components.
This is the factor map. -/
@[simps!]
noncomputable
def RingHom.projPiIndex {ι S : Type*} {R : ι → Type*} [_root_.Finite ι] [DecidableEq ι]
    [∀ i, Semiring (R i)] [Semiring S] [IsDomain S] (f : (Π i, R i) →+* S) :
    R f.piIndex →+* S where
  __ := f.toNonUnitalRingHom.comp (NonUnitalRingHom.single R f.piIndex)
  map_one' := by simp

/-- `Hom(∏ Rᵢ, S) ≃ ∐ Hom(Rᵢ, S)` when `S` is a domain. -/
@[simps! apply_fst apply_snd symm_apply_apply]
noncomputable
def Pi.ringHomEquivOfIsDomain {ι S : Type*} {R : ι → Type*} [Finite ι] [DecidableEq ι]
    [∀ i, Ring (R i)] [Ring S] [IsDomain S] :
    ((Π i, R i) →+* S) ≃ Σ i, R i →+* S where
  toFun f := ⟨f.piIndex, f.projPiIndex⟩
  invFun f := f.2.comp (Pi.evalRingHom R f.1)
  left_inv f := by ext; simp
  right_inv f := by
    have : Function.Injective (fun f : Σ i, R i →+* S ↦ f.2.comp (Pi.evalRingHom R f.1)) := by
      intro ⟨i₁, f₁⟩ ⟨i₂, f₂⟩ e
      obtain rfl : i₁ = i₂ := by
        by_contra H; simpa [H] using DFunLike.congr_fun e (Pi.single i₁ 1)
      congr 1
      ext x
      simpa using DFunLike.congr_fun e (Pi.single i₁ x)
    exact this (by ext; simp)

/-- `Hom(∏ Rᵢ, S) ≃ ∐ Hom(Rᵢ, S)` when `S` is a domain.
This is the `AlgHom` version of `Pi.ringHomEquivOfIsDomain`. -/
@[simps! apply_fst symm_apply_apply, simps! -isSimp apply_snd_apply]
noncomputable
def Pi.algHomEquivOfIsDomain {ι R₀ S : Type*} {R : ι → Type*} [Finite ι] [DecidableEq ι]
    [CommSemiring R₀]
    [∀ i, Ring (R i)] [∀ i, Algebra R₀ (R i)] [Ring S] [Algebra R₀ S] [IsDomain S] :
    ((Π i, R i) →ₐ[R₀] S) ≃ Σ i, (R i →ₐ[R₀] S) where
  toFun f := ⟨_, f.projPiIndex, fun r ↦ (f.single_piIndex _).trans (f.commutes r)⟩
  invFun f := f.2.comp (Pi.evalAlgHom R₀ R f.1)
  left_inv f := by ext; simp
  right_inv f := by
    let emb : (Σ i, (R i →ₐ[R₀] S)) → (Σ i, (R i →+* S)) := Sigma.map id fun _ ↦ AlgHom.toRingHom
    have : emb.Injective := Function.Injective.sigma_map (fun _ _ e ↦ e)
        fun _ a b e ↦ AlgHom.ext (DFunLike.congr_fun e :)
    apply this
    exact Pi.ringHomEquivOfIsDomain.apply_symm_apply ⟨f.1, f.2.toRingHom⟩

open MulAction IntermediateField in
/-- If `G` is a closed subgroup of the galois group `Γ := Gal(L/K)`, then
`Γ/G` is in bijection with the `K`-linear embeddings of `Lᴳ` into `L`.

Note that `G` is not necessarily normal here. -/
noncomputable
def InfiniteGalois.quotientEquivFixedFieldEmb [IsGalois K L] (G : ClosedSubgroup (L ≃ₐ[K] L)) :
    ((L ≃ₐ[K] L) ⧸ G.1) ≃ (fixedField G.1 →ₐ[K] L) where
  toFun := Quotient.lift (fun σ ↦ σ.toAlgHom.comp (IntermediateField.val _)) (by
    rintro _ σ ⟨τ, rfl⟩
    ext x
    change σ _ = σ _
    simpa using x.2 ⟨_, τ.2⟩)
  invFun f := QuotientGroup.mk (.ofBijective (f.liftNormal L) (AlgHom.normal_bijective K L L _))
  left_inv := Quotient.ind fun σ ↦ show _ = QuotientGroup.mk σ by
    simp only [AlgEquiv.toAlgHom_eq_coe, Quotient.lift_mk, QuotientGroup.eq]
    conv_lhs => rw [← InfiniteGalois.fixingSubgroup_fixedField G]
    intro x
    rw [mul_smul, inv_smul_eq_iff]
    exact ((σ.toAlgHom.comp (IntermediateField.val _)).liftNormal_commutes _ _).symm
  right_inv f := by ext x; simpa using f.liftNormal_commutes _ _

instance {R S T G : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Monoid G] [MulSemiringAction G T] [SMulCommClass G R T] : MulAction G (S →ₐ[R] T) where
  smul g := (MulSemiringAction.toAlgHom _ _ g).comp
  one_smul f := by ext x; exact one_smul G (f x)
  mul_smul g g' f := by ext x; exact mul_smul g g' (f x)

/-- Evaluating a `MulActionHom` is an `AlgHom`, bundled as a `MulActionHom`. -/
def MulActionHom.evalAlgHom (G R X Y : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [Monoid G] [MulAction G X] [MulSemiringAction G Y] [SMulCommClass G R Y] :
    X →[G] ((X →[G] Y) →ₐ[R] Y) where
  toFun x := (Pi.evalAlgHom _ _ x).comp MulActionHom.toFunAlgHom
  map_smul' σ x := by ext f; exact f.map_smul σ x

@[simp]
lemma MulActionHom.evalAlgHom_apply {G R X Y : Type*} [CommSemiring R] [Semiring Y] [Algebra R Y]
    [Monoid G] [MulAction G X] [MulSemiringAction G Y] [SMulCommClass G R Y] (x f) :
    evalAlgHom G R X Y x f = f x := rfl

/-- Given a representative for each orbit of `X` under `G`, and for each `x : X` a choice of `σ`
that sends `x` to the representative, we obtain a bijection between `X` and `∐ G/stab(x)` where
the disjoint union runs through the representatives. -/
@[simps]
def MulAction.sigmaRangeQuotientStabilizer
    {G X : Type*} [Group G] [MulAction G X]
    (σ : X → G) (hσ : ∀ a b, orbitRel G X a b → σ a • a = σ b • b) :
    (Σ i : Set.range (fun i ↦ σ i • i), G ⧸ stabilizer G i.1) ≃ X :=
  letI Y := Σ i : Set.range (fun i ↦ σ i • i), G ⧸ stabilizer G i.1
  letI f : Y → X := fun x ↦ ofQuotientStabilizer _ _ x.2
  letI g : X → Y := fun x ↦ ⟨⟨_, x, rfl⟩, ↑((σ x)⁻¹)⟩
  haveI hf : f.Injective := by
    intro ⟨⟨ia, xa, ha⟩, fa⟩ ⟨⟨ib, xb, hb⟩, fb⟩ e
    obtain ⟨fa, rfl⟩ := QuotientGroup.mk_surjective fa
    obtain ⟨fb, rfl⟩ := QuotientGroup.mk_surjective fb
    have : orbitRel G X xa xb := by
      trans fa • ia
      · symm; exact ⟨fa * σ xa, by rw [← ha, ← mul_smul]⟩
      · rw [show fa • ia = fb • ib from e]; exact ⟨fb * σ xb, by rw [← hb, ← mul_smul]⟩
    obtain rfl : ia = ib := (ha.symm.trans (hσ xa xb this)).trans hb
    congr 1
    simpa [QuotientGroup.eq, mul_smul, inv_smul_eq_iff] using e.symm
  haveI hfg : Function.RightInverse g f := fun x ↦ inv_smul_smul (σ x) x
  ⟨f, g, fun x ↦ hf (hfg (f x)), hfg⟩

open MulAction in
lemma InfiniteGalois.evalAlgHom_bijective [IsGalois K L] [Finite X]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) X] :
    Function.Bijective (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K X L) := by
  classical
  choose φ hφ using Quotient.mk_surjective (s := orbitRel (L ≃ₐ[K] L) X)
  choose σ hσ using fun x ↦ Quotient.eq''.mp (hφ ⟦x⟧)
  replace hσ : ∀ a b, orbitRel (L ≃ₐ[K] L) X a b → σ a • a = σ b • b :=
    fun a b e ↦ ((hσ a).trans (congr_arg φ (Quotient.eq''.mpr e))).trans (hσ b).symm
  let e : ((X →[L ≃ₐ[K] L] L) →ₐ[K] L) ≃ X := by
    refine (AlgEquiv.arrowCongr (MulAction.etaleSubalgebraEquiv K L X σ hσ) .refl).trans ?_
    refine Pi.algHomEquivOfIsDomain.trans ?_
    refine (Equiv.sigmaCongrRight fun _ ↦
      (InfiniteGalois.quotientEquivFixedFieldEmb K L ⟨_, ?_⟩).symm).trans ?_
    · exact Subgroup.isClosed_of_isOpen _ (ContinuousSMulDiscrete.isOpen_stabilizer _ _)
    exact MulAction.sigmaRangeQuotientStabilizer σ hσ
  convert e.symm.bijective
  ext x f
  change f x = (σ x)⁻¹ • (f (σ x • x))
  rw [map_smul, inv_smul_smul]

open MulAction IntermediateField in
instance [IsGalois K L] [Finite X] : Algebra.FormallyEtale K (X →[L ≃ₐ[K] L] L) := by
  classical
  choose φ hφ using Quotient.mk_surjective (s := orbitRel (L ≃ₐ[K] L) X)
  choose σ hσ using fun x ↦ Quotient.eq''.mp (hφ ⟦x⟧)
  replace hσ : ∀ a b, orbitRel (L ≃ₐ[K] L) X a b → σ a • a = σ b • b :=
    fun a b e ↦ ((hσ a).trans (congr_arg φ (Quotient.eq''.mpr e))).trans (hσ b).symm
  have (x : X) : Algebra.FormallyEtale K (fixedField (stabilizer (L ≃ₐ[K] L) x)) :=
    .of_isSeparable _ _
  exact .of_equiv (MulAction.etaleSubalgebraEquiv K L X σ hσ).symm

open MulAction IntermediateField in
instance [IsGalois K L] [Finite X] [ContinuousSMulDiscrete (L ≃ₐ[K] L) X] :
    Module.Finite K (X →[L ≃ₐ[K] L] L) := by
  classical
  choose φ hφ using Quotient.mk_surjective (s := orbitRel (L ≃ₐ[K] L) X)
  choose σ hσ using fun x ↦ Quotient.eq''.mp (hφ ⟦x⟧)
  replace hσ : ∀ a b, orbitRel (L ≃ₐ[K] L) X a b → σ a • a = σ b • b :=
    fun a b e ↦ ((hσ a).trans (congr_arg φ (Quotient.eq''.mpr e))).trans (hσ b).symm
  have (x : X) : Module.Finite K (fixedField (stabilizer (L ≃ₐ[K] L) x)) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by
      rw [InfiniteGalois.fixingSubgroup_fixedField
        ⟨_, Subgroup.isClosed_of_isOpen _ (ContinuousSMulDiscrete.isOpen_stabilizer _ _)⟩]
      exact ContinuousSMulDiscrete.isOpen_stabilizer _ _)
  exact .equiv (MulAction.etaleSubalgebraEquiv K L X σ hσ).toLinearEquiv.symm

instance [IsGalois K L] [Finite X] [ContinuousSMulDiscrete (L ≃ₐ[K] L) X] :
    Algebra.Etale K (X →[L ≃ₐ[K] L] L) where
  finitePresentation := by rw [← Algebra.FinitePresentation.of_finiteType]; infer_instance

/-- Evaluating a `AlgHom` is an `MulActionHom`, bundled as a `AlgHom`. -/
def AlgHom.evalMulActionHom (G R A Y : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [Monoid G] [Semiring A] [Algebra R A] [MulSemiringAction G Y] [SMulCommClass G R Y] :
    A →ₐ[R] ((A →ₐ[R] Y) →[G] Y) where
  toFun a := ⟨fun f ↦ f a, fun g f ↦ rfl⟩
  map_one' := by ext f; exact map_one f
  map_mul' a b := by ext f; exact map_mul f a b
  map_zero' := by ext f; exact map_zero f
  map_add' a b := by ext f; exact map_add f a b
  commutes' r := by ext f; exact f.commutes r

variable (A : Type u) [CommRing A] [Algebra K A]

instance [Module.Finite K A] : ContinuousSMulDiscrete (L ≃ₐ[K] L) (A →ₐ[K] L) := by
  refine continuousSMulDiscrete_iff_isOpen_stabilizer.mpr fun f ↦ ?_
  have : FiniteDimensional K f.range :=
    .of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  let E := IntermediateField.adjoin K (f.range : Set L)
  have : FiniteDimensional K E := by
    show FiniteDimensional K E.toSubalgebra
    rwa [IntermediateField.adjoin_algebraic_toSubalgebra, Algebra.adjoin_eq]
    simp only [AlgHom.coe_range, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact fun x ↦ ((Algebra.IsIntegral.isIntegral (R := K) x).map f).isAlgebraic
  refine Subgroup.isOpen_mono ?_ E.fixingSubgroup_isOpen
  intro σ hσ
  ext x
  exact hσ ⟨f x, IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩⟩

attribute [local instance] Ideal.Quotient.field RingHom.ker_isPrime in
lemma InfiniteGalois.evalMulActionHom_bijective [Algebra.Etale K A] [IsGalois K L]
    (H : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → Nonempty (A ⧸ 𝔪 →ₐ[K] L)) :
    Function.Bijective (AlgHom.evalMulActionHom (L ≃ₐ[K] L) K A L) := by
  let emb (𝔪 : Ideal A) [𝔪.IsMaximal] := (H 𝔪 ‹_›).some
  have := Algebra.FormallyUnramified.isReduced_of_field K A
  have := Algebra.FormallyUnramified.finite_of_free K A
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  have hemb (𝔪 : Ideal A) [𝔪.IsMaximal] (f : (A →ₐ[K] L) →[(L ≃ₐ[K] L)] L) :
      f ((emb 𝔪).comp (Ideal.Quotient.mkₐ _ _)) ∈ (emb 𝔪).fieldRange := by
    rw [← fixedField_fixingSubgroup (emb 𝔪).fieldRange]
    intro ⟨σ, hσ⟩
    rw [Subgroup.mk_smul, ← map_smul]
    congr 1
    ext x
    simpa using hσ ⟨_, Ideal.Quotient.mk _ x, rfl⟩
  choose! F' hF' using hemb
  let F : ((A →ₐ[K] L) →[(L ≃ₐ[K] L)] L) → A :=
    fun f ↦ (IsArtinianRing.equivPi A).symm fun 𝔪 ↦ F' 𝔪.1 f
  have H₁ : Function.LeftInverse F (AlgHom.evalMulActionHom (L ≃ₐ[K] L) K A L) := by
    intros a
    apply (IsArtinianRing.equivPi A).injective
    refine ((IsArtinianRing.equivPi A).apply_symm_apply _).trans ?_
    ext ⟨𝔪, h𝔪⟩
    replace h𝔪 : 𝔪.IsMaximal := h𝔪
    exact (emb 𝔪).injective (hF' _ _)
  have H₂ : Function.Injective F := by
    intros f₁ f₂ e
    ext g
    obtain ⟨σ, hσ⟩ : ∃ σ : L ≃ₐ[K] L, σ • emb (RingHom.ker g) = Ideal.kerLiftAlg g := by
      letI := (emb (RingHom.ker g)).toAlgebra
      have : IsScalarTower K (A ⧸ RingHom.ker g) L :=
        .of_algebraMap_eq' (emb (RingHom.ker g)).comp_algebraMap.symm
      exact ⟨.ofBijective ((Ideal.kerLiftAlg g).liftNormal L) (AlgHom.normal_bijective _ _ _ _),
        AlgHom.ext ((Ideal.kerLiftAlg g).liftNormal_commutes L)⟩
    have hσ' : σ • (emb (RingHom.ker g)).comp (Ideal.Quotient.mkₐ _ _) = g :=
      AlgHom.ext fun x ↦ DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)
    rw [← hσ', map_smul, map_smul, ← hF', ← hF']
    congr 2
    exact congr_fun ((IsArtinianRing.equivPi A).symm.injective e)
      ⟨RingHom.ker g, inferInstanceAs (RingHom.ker g).IsMaximal⟩
  exact ⟨H₁.injective, fun x ↦ ⟨F x, H₂ (H₁ (F x))⟩⟩

attribute [local instance] Ideal.Quotient.field Algebra.FormallyUnramified.isSeparable in
lemma InfiniteGalois.evalMulActionHom_bijective_of_isSepClosed
    [Algebra.Etale K A] [IsGalois K L] [IsSepClosed L] :
    Function.Bijective (AlgHom.evalMulActionHom (L ≃ₐ[K] L) K A L) :=
  InfiniteGalois.evalMulActionHom_bijective _ _ _ fun _ _ ↦ ⟨IsSepClosed.lift⟩

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass in
noncomputable
instance {A : Type*} [CommRing A] [Bialgebra K A] : Monoid (A →ₐ[K] L) where
  mul f g := .comp (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)) (Bialgebra.comulAlgHom K A)
  mul_assoc a b c := by
    ext x
    convert congr(Algebra.TensorProduct.lift a (Algebra.TensorProduct.lift b c (fun _ _ ↦ .all _ _))
      (fun _ _ ↦ .all _ _) $(Coalgebra.coassoc_apply (R := K) x))
    · change Algebra.TensorProduct.lift _ c (fun _ _ ↦ .all _ _) (Coalgebra.comul x) = _
      induction Coalgebra.comul (R := K) x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul x y =>
        change (Algebra.TensorProduct.lift a b (fun _ _ ↦ .all _ _) (Coalgebra.comul x)) * _ = _
        dsimp
        induction Coalgebra.comul (R := K) x with
        | zero => simp only [map_zero, zero_mul, TensorProduct.zero_tmul]
        | add x y _ _ => simp only [map_add, add_mul, TensorProduct.add_tmul, *]
        | tmul x z => exact mul_assoc _ _ _
    · change Algebra.TensorProduct.lift a _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x) = _
      induction Coalgebra.comul (R := K) x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul x y => rfl
  one := (Algebra.ofId K L).comp (Bialgebra.counitAlgHom K A)
  one_mul f := by
    ext x
    change Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x) = _
    convert congr(Algebra.TensorProduct.lift (Algebra.ofId K L)
      f (fun _ _ ↦ .all _ _) $(Coalgebra.rTensor_counit_comul (R := K) x))
    · induction Coalgebra.comul (R := K) x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul x y =>
        simp only [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul]
        rfl
    · simp
  mul_one f := by
    ext x
    change Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x) = _
    convert congr(Algebra.TensorProduct.lift f (Algebra.ofId K L) (fun _ _ ↦ .all _ _)
      $(Coalgebra.lTensor_counit_comul (R := K) x))
    · induction Coalgebra.comul (R := K) x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul x y =>
        simp only [Algebra.TensorProduct.lift_tmul]
        rfl
    · simp

noncomputable
instance {A : Type*} [CommRing A] [Bialgebra K A] :
    MulDistribMulAction (L ≃ₐ[K] L) (A →ₐ[K] L) where
  smul_mul r f g := by
    ext x
    change r (Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x)) =
      Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x)
    induction Coalgebra.comul (R := K) x with
    | zero => simp only [map_zero]
    | add x y _ _ => simp only [map_add, *]
    | tmul x y => simp; rfl
  smul_one r := by
    ext x
    change r (algebraMap _ _ _) = _
    simp
    rfl

noncomputable
instance {A : Type*} [CommRing A] [Bialgebra K A] :
    MulDistribMulAction (L ≃ₐ[K] L) (A →ₐ[K] L) where
  smul_mul r f g := by
    ext x
    change r (Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x)) =
      Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x)
    induction Coalgebra.comul (R := K) x with
    | zero => simp only [map_zero]
    | add x y _ _ => simp only [map_add, *]
    | tmul x y => simp; rfl
  smul_one r := by
    ext x
    change r (algebraMap _ _ _) = _
    simp
    rfl

noncomputable
instance {A : Type*} [CommRing A] [Bialgebra K A] :
    MulDistribMulAction (L ≃ₐ[K] L) (A →ₐ[K] L) where
  smul_mul r f g := by
    ext x
    change r (Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x)) =
      Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x)
    induction Coalgebra.comul (R := K) x with
    | zero => simp only [map_zero]
    | add x y _ _ => simp only [map_add, *]
    | tmul x y => simp; rfl
  smul_one r := by
    ext x
    change r (algebraMap _ _ _) = _
    simp
    rfl
