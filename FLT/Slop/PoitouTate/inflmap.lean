/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import Mathlib

/-!
# Functoriality of continuous cohomology

Given topological groups `G` and `H`, a continuous group homomorphism `φ : H →ₜ* G`, a topological
representation `X` of `G`, a topological representation `Y` of `H`, and a morphism of topological
`H`-representations `f : res φ X ⟶ Y`, we construct a cochain map
`homogeneousCochains X ⟶ homogeneousCochains Y` and hence maps on continuous cohomology
`Hⁿ(G, X) ⟶ Hⁿ(H, Y)`.

## Main definitions

* `ContinuousCohomology.cochainsMap φ f` : the cochain map
  `homogeneousCochains X ⟶ homogeneousCochains Y` induced by `φ : H →ₜ* G` and
  `f : res φ X ⟶ Y`, sending an invariant function `σ : C(G, C(G, ⋯))` to `f ∘ σ ∘ φ`.
* `ContinuousCohomology.map φ f n` : the induced map `Hⁿ(G, X) ⟶ Hⁿ(H, Y)` on continuous
  cohomology.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Functor

namespace ContinuousCohomology

open TopRep ContRepresentation

variable {k : Type u} {G H K : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  {X X' X'' : TopRep k G} {Y : TopRep k H} {Z : TopRep k K}

instance (φ : H →* G) : (resFunctor (k := k) φ).Additive where

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
lemma _root_.TopRep.ofHom_comp {A B C : Type w}
    [AddCommGroup A] [Module k A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousSMul k A]
    [AddCommGroup B] [Module k B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [ContinuousSMul k B]
    [AddCommGroup C] [Module k C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    [ContinuousSMul k C]
    {ρ : ContRepresentation k G A} {σ : ContRepresentation k G B}
    {τ : ContRepresentation k G C} (f : ρ →ⁱL σ) (g : σ →ⁱL τ) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

omit [TopologicalSpace k] [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
lemma _root_.ContIntertwiningMap.comp_id {A B : Type w}
    [AddCommGroup A] [Module k A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [Module k B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    {ρ : ContRepresentation k G A} {σ : ContRepresentation k G B} (f : ρ →ⁱL σ) :
    f.comp .id = f := rfl

omit [TopologicalSpace k] [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
lemma _root_.ContIntertwiningMap.id_comp {A B : Type w}
    [AddCommGroup A] [Module k A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [Module k B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    {ρ : ContRepresentation k G A} {σ : ContRepresentation k G B} (f : ρ →ⁱL σ) :
    ContIntertwiningMap.id.comp f = f := rfl

@[simp]
lemma _root_.ContRepresentation.coind₁Res_id {A : Type w}
    [AddCommGroup A] [Module k A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousSMul k A] (π : ContRepresentation k G A) :
    coind₁Res (ContinuousMonoidHom.id G) π = .id := rfl

/-- The morphism between the `i`-th levels of the standard (coinduced) resolutions of `X` and
`X'` induced by a morphism `f : X ⟶ X'`, applying `f` pointwise under the iterated
coinduction. -/
abbrev resolutionMap₁ (f : X ⟶ X') :
    (i : ℕ) → (resolutionX X i) ⟶ (resolutionX X' i)
  | 0 => f
  | i + 1 => ((coind₁Functor k G).map (resolutionMap₁ f i))

lemma resolutionMap₁_zero (f : X ⟶ X') : resolutionMap₁ f 0 = f := rfl

lemma resolutionMap₁_succ (f : X ⟶ X') (n : ℕ) :
    resolutionMap₁ f (n + 1) = (coind₁Functor k G).map (resolutionMap₁ f n) := rfl

/-- The maps `resolutionMap₁ f` commute with the differentials of the resolutions. -/
lemma resolutionMap₁_comp_d (f : X ⟶ X') (i : ℕ) :
    resolutionMap₁ f i ≫ d X' i = (d X i) ≫ resolutionMap₁ f (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [d_succ, d_succ, resolutionMap₁_succ f (i + 1), Preadditive.comp_sub,
      Preadditive.sub_comp]
    congr 1
    rw [resolutionMap₁_succ f i, ← Functor.map_comp, ← Functor.map_comp, ih]

lemma resolutionMap₁_id (i : ℕ) : resolutionMap₁ (𝟙 X) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rw [resolutionMap₁_zero]
  | succ _ ih => rw [resolutionMap₁_succ, ih, CategoryTheory.Functor.map_id]

lemma resolutionMap₁_comp (f : X ⟶ X') (f' : X' ⟶ X'') (i : ℕ) :
    resolutionMap₁ (f ≫ f') i = (resolutionMap₁ f i) ≫ resolutionMap₁ f' i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [resolutionMap₁_succ, resolutionMap₁_succ, resolutionMap₁_succ, ih,
      CategoryTheory.Functor.map_comp]

variable (k G)
/-- The standard (coinduced) resolution `resolution'`, made functorial in the representation: a
morphism `f : X ⟶ Y` induces the levelwise maps `resolutionMap₁ f`, which commute with the
differentials. -/
@[simps] abbrev resolution'Functor : TopRep k G ⥤ CochainComplex (TopRep k G) ℕ where
  obj           := resolution'
  map {X Y} f   := {
    f n   := resolutionMap₁ f (n + 1)
    comm' := by simp +contextual [resolution'd_eq, resolutionMap₁_comp_d f _]
  }
  map_id _      := HomologicalComplex.hom_ext _ _ <| fun _ ↦ resolutionMap₁_id _
  map_comp _ _  := HomologicalComplex.hom_ext _ _ <| fun _ ↦ resolutionMap₁_comp _ _ _

/-- The homogeneous cochain complex computing continuous cohomology, made functorial in the
representation: form the standard resolution and take `G`-invariants levelwise. -/
abbrev homogeneousCochainsFunctor : TopRep k G ⥤ CochainComplex (TopModuleCat k) ℕ :=
    resolution'Functor k G ⋙ (invariantsFunctor k G).mapHomologicalComplex (.up ℕ)

lemma homogeneousCochainsFunctor_obj :
    (homogeneousCochainsFunctor k G).obj = homogeneousCochains := rfl

/-- Continuous cohomology `Hⁿ(G, -)` as a functor from topological representations of `G` to
topological modules: the `n`-th homology of the homogeneous cochain complex. -/
noncomputable abbrev Functor (n : ℕ) : TopRep k G ⥤ TopModuleCat k :=
    homogeneousCochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- `Hₜ n` is notation for `continuousCohomology n`, the `n`-th continuous cohomology of a
topological representation. -/
notation "Hₜ" => continuousCohomology

lemma Functor_obj (n : ℕ) : (Functor k G n).obj = Hₜ n := rfl

variable {k G}
variable (X) in
/-- The morphisms between the levels of the standard resolutions of `X` and `Y` induced by a
continuous group homomorphism `φ : H →ₜ* G` and a morphism `f : res φ X ⟶ Y`, given by
`F ↦ f ∘ F ∘ φ`. -/
abbrev _root_.TopRep.resolutionXRes (φ : H →ₜ* G) :
    (i : ℕ) → (res φ (resolutionX X i)) ⟶ (resolutionX (res φ.toMonoidHom X) i)
  | 0 => 𝟙 _
  | i + 1 => ofHom (coind₁ResMap φ (resolutionXRes φ i).hom)

lemma resolutionXRes_zero (φ : H →ₜ* G) : X.resolutionXRes φ 0 = 𝟙 _ := rfl

lemma resolutionXRes_one (φ : H →ₜ* G) : X.resolutionXRes φ 1 = ofHom (coind₁ResMap φ .id) := rfl

lemma resolutionXRes_succ (φ : H →ₜ* G) (i : ℕ) :
    resolutionXRes X φ (i + 1) = ofHom (coind₁ResMap φ (resolutionXRes _ φ i).hom) := rfl

@[simp]
lemma resolutionXRes_id (X : TopRep k G) (i : ℕ) :
    resolutionXRes X (ContinuousMonoidHom.id G) i = 𝟙 (resolutionX X i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionXRes_succ, ih]
    ext; rfl


lemma resolutionXRes_comp (φ : H →ₜ* G) (ψ : K →ₜ* H) (i : ℕ) :
    resolutionXRes X (φ.comp ψ) i =
      (resFunctor ψ.toMonoidHom).map (resolutionXRes X φ i) ≫ resolutionXRes _ ψ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionXRes_succ, resolutionXRes_succ, resolutionXRes_succ, ih]
    ext; rfl

/-- The maps `resolutionMap φ f` commute with the differentials of the resolutions. -/
lemma resolutionXRes_comp_d (φ : H →ₜ* G) (i : ℕ) :
    resolutionXRes X φ i ≫ d _ i =
      (resFunctor (φ : H →* G)).map (d X i) ≫ resolutionXRes X φ (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext : 1
    replace ih := congr($(ih).hom)
    simp only [TopRep.hom_comp, TopRep.hom_ofHom, hom_d_succ,
      ContIntertwiningMap.restrict_sub, ContIntertwiningMap.sub_comp,
      ContIntertwiningMap.comp_sub, coind₁Map_comp_coind₁ResMap,
      coind₁ResMap_comp_coind₁Map_restrict] at ih ⊢
    rw [ih, ← coind₁ResMap_comp_coind₁ι_restrict]

/-- The maps `resolutionXRes X φ` are natural in `X`. -/
lemma resolutionXRes_naturality (φ : H →ₜ* G) (f : X ⟶ X') (i : ℕ) :
    (resFunctor (φ : H →* G)).map (resolutionMap₁ f i) ≫ resolutionXRes X' φ i =
      resolutionXRes X φ i ≫ resolutionMap₁ ((resFunctor φ.toMonoidHom).map f) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionXRes_succ, resolutionXRes_succ, resolutionMap₁_succ, resolutionMap₁_succ]
    ext F x
    exact congr($(ih).hom (F (φ x)))

instance (φ : H →* G) : (resFunctor (k := k) φ).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The cochain map from the restriction along `φ : H →ₜ* G` of the standard resolution of `X`
to the standard resolution of the restricted representation `res φ X`, given levelwise by
`resolutionXRes` (`F ↦ F ∘ φ`). -/
abbrev resolution'Res (φ : H →ₜ* G) :
    ((resFunctor φ.toMonoidHom).mapHomologicalComplex (.up ℕ)).obj (resolution' X)
    ⟶ resolution' (res φ.toMonoidHom X) where
  f n := resolutionXRes X φ (n + 1)
  comm' := by
    intro _ _ rfl
    simp only [mapHomologicalComplex_obj_d, ContinuousMonoidHom.coe_toMonoidHom,
      CochainComplex.of_d, resolution'd_eq]
    exact resolutionXRes_comp_d φ _

/-- The cochain maps `resolution'Res φ` assembled into a natural transformation: forming the
standard resolution over `G` and then restricting along `φ : H →ₜ* G` maps naturally to
restricting the representation first and then resolving over `H`. -/
def resolution'ResNatTrans (φ : H →ₜ* G) :
    resolution'Functor k G ⋙ (resFunctor ↑φ).mapHomologicalComplex (.up ℕ)
    ⟶ (resFunctor φ) ⋙ resolution'Functor k H where
  app X := resolution'Res φ
  naturality X Y f := by
    ext n : 1
    exact resolutionXRes_naturality φ f (n + 1)

/-- A `G`-invariant vector is in particular invariant under the image of `φ : H →* G`: the
inclusion of the `G`-invariants of `X` into the `H`-invariants of the restriction `X.res φ`. -/
def _root_.TopRep.invariantsRes (φ : H →* G) (X : TopRep k G) :
    X.invariants ⟶ (X.res φ).invariants :=
  TopModuleCat.ofHom (ContIntertwiningMap.mapInvariantsOfRes φ ContIntertwiningMap.id)

/-- The inclusions `invariantsRes φ` assembled into a natural transformation from the
`G`-invariants functor to restriction along `φ : H →* G` followed by the `H`-invariants
functor. -/
abbrev _root_.TopRep.invariantsResNatTrans (φ : H →* G) :
    invariantsFunctor k G ⟶ resFunctor φ ⋙ invariantsFunctor k H where
  app := invariantsRes φ
  naturality X Y f := (eq_of_comp_right_eq'
    (invariantsRes φ X ≫ (resFunctor φ ⋙ invariantsFunctor k H).map f)
    ((invariantsFunctor k G).map f ≫ invariantsRes φ Y) rfl).symm

/-- The degree-`n` component of the restriction map on homogeneous cochains induced by a
continuous group homomorphism `φ : H →ₜ* G`, sending an invariant cochain
`σ : C(G, C(G, ⋯))` to `σ ∘ φ`. -/
def _root_.TopRep.homogeneousCochainsXRes (φ : H →ₜ* G) (X : TopRep k G) (n : ℕ) :
    X.homogeneousCochains.X n ⟶ (X.res φ.toMonoidHom).homogeneousCochains.X n :=
  (X.resolutionX _).invariantsRes φ.toMonoidHom ≫ ((invariantsFunctor (k := k) (G := H)).map
  (resolutionXRes X φ _))

lemma _root_.TopRep.homogeneousCochainsXRes_zero (φ : H →ₜ* G) (X : TopRep k G) :
    X.homogeneousCochainsXRes φ 0 =
    X.coind₁.invariantsRes φ ≫ (invariantsFunctor k H).map (ofHom (coind₁ResMap φ .id)) := rfl

lemma _root_.TopRep.homogeneousCochainsXRes_succ (φ : H →ₜ* G) (X : TopRep k G) (n : ℕ) :
    X.homogeneousCochainsXRes φ (n + 1) =
    (X.resolution'X n).coind₁.invariantsRes φ ≫ (invariantsFunctor k H).map
    (ofHom (coind₁ResMap φ (X.resolutionXRes φ (n + 1)).hom)) := rfl

variable (k) in
/-- The restriction maps on homogeneous cochain complexes induced by `φ : H →ₜ* G`, as a natural
transformation from the cochain complex functor for `G` to restriction along `φ` followed by the
cochain complex functor for `H`. -/
def homogeneousCochainsResNatTrans (φ : H →ₜ* G) : homogeneousCochainsFunctor k G
    ⟶ (resFunctor φ.toMonoidHom) ⋙ homogeneousCochainsFunctor k H :=
  (𝟙 (resolution'Functor k G)
    ◫ ((invariantsResNatTrans φ.toMonoidHom (k := k)).mapHomologicalComplex _
    ≫ (mapHomologicalComplexCompIso (.refl _) _).inv))
  ≫ (Functor.associator _ _ _).inv
  ≫ (resolution'ResNatTrans φ ◫ (𝟙 _))
  ≫ (Functor.associator _ _ _).hom

lemma homogeneousCochainsResNatTrans_app_f (φ : H →ₜ* G) (X : TopRep k G) (n : ℕ) :
    ((homogeneousCochainsResNatTrans k φ).app X).f n = homogeneousCochainsXRes φ X n := rfl

variable (k) in
/-- The map on continuous cohomology `Hⁿ(G, X) ⟶ Hⁿ(H, res φ X)` induced by a continuous group
homomorphism `φ : H →ₜ* G`, as a natural transformation between the cohomology functors. -/
noncomputable abbrev resNatTrans (φ : H →ₜ* G) (n : ℕ) :
    (Functor k G n) ⟶ (resFunctor φ.toMonoidHom ⋙ Functor k H n) :=
  homogeneousCochainsResNatTrans k φ ◫ 𝟙 _

end ContinuousCohomology

/-!
Define inflation maps in continuous cohomology.
-/

universe u₁ u₂ u₃
open CategoryTheory
  TopRep
  ContRepresentation

variable {R : Type u₁} [CommRing R]
variable {G H : Type u₂} [Group G] [Group H]

namespace ContRepresentation

variable {V W : Type u₃} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [Module R V] (ρ : ContRepresentation R G V)
    [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [Module R W] (ρ' : ContRepresentation R G W)
    (N : Subgroup G)


/--
For `ρ : ContRepresentation R G V`,= and a subgroup `N` of `G`,
`ρ.relInvariants N` is the `R`-submodule of `V` consisting of the `N`-invariant elements.
-/
def relInvariants : Submodule R V where
  carrier := {v : V | ∀ n ∈ N, ρ n v = v}
  add_mem' h₁ h₂ _ h  := by rw [_root_.map_add, h₁, h₂] <;> exact h
  zero_mem' _ _       := map_zero _
  smul_mem' _ _ h _ _ := by rwa [_root_.map_smul, h]

variable [hN : N.Normal]
lemma rho_mem_relInvariants {v : V} (hv : v ∈ ρ.relInvariants N) (g : G) :
    ρ g v ∈ ρ.relInvariants N := by
  intro n hn
  calc
    _ = ρ (n * g) v             := by rw [map_mul, mul_apply_eq_comp]
    _ = ρ (g * (g⁻¹ * n * g)) v := by simp_rw [←mul_assoc, mul_inv_cancel, one_mul]
    _ = ρ g (ρ (g⁻¹ * n * g) v) := by rw [map_mul, mul_apply_eq_comp]
    _ = ρ g v                   := by rw [hv _ (Subgroup.Normal.conj_mem' hN n hn g)]

/-- For a normal subgroup `N` of `G`, the action of `G` on `V` preserves the `N`-invariants
(conjugation by `g` keeps elements of `N` in `N`), so `G` acts on `ρ.relInvariants N` by
restriction. -/
@[simps] def relInvariantsRho : ContRepresentation R G (ρ.relInvariants N) := ⟨{
  toFun g       := (ρ g).restrict (fun _ hv ↦ ρ.rho_mem_relInvariants N hv g)
  map_one'      := by ext; simp
  map_mul' _ _  := by ext; simp
}⟩

/-- An intertwining map `f : ρ →ⁱL ρ'` sends `N`-invariant vectors to `N`-invariant vectors, so
it restricts to an intertwining map between the `G`-representations on the `N`-invariants. -/
def relInvariantsIntertwining (f : ρ →ⁱL ρ') :
    ρ.relInvariantsRho N →ⁱL ρ'.relInvariantsRho N where
  toContinuousLinearMap := f.toContinuousLinearMap.restrict (by
    intro v hv n hn
    have := (f.isIntertwining n v).symm
    rwa [hv n hn] at this)
  isIntertwining' g := by
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_restrict_apply]
    exact f.isIntertwining g v

lemma le_relInvariantsRho_ker : N ≤ (ρ.relInvariantsRho N).toMonoidHom.ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  ext ⟨_,hv⟩
  apply hv _ hn

/-- Since `N` acts trivially on the `N`-invariants, the `G`-action on `ρ.relInvariants N`
descends to a continuous representation of the quotient group `G ⧸ N`. -/
def relInvariantsInfl : ContRepresentation R (G ⧸ N) (ρ.relInvariants N) :=
  ⟨QuotientGroup.lift N (ρ.relInvariantsRho N) (ρ.le_relInvariantsRho_ker N)⟩

/-- The restriction `relInvariantsIntertwining` of an intertwining map `f : ρ →ⁱL ρ'` to the
`N`-invariants, viewed as an intertwining map of the descended `G ⧸ N`-representations. -/
def relInvariantsIntertwining' (f : ρ →ⁱL ρ') :
    ρ.relInvariantsInfl N →ⁱL ρ'.relInvariantsInfl N where
  toContinuousLinearMap := (relInvariantsIntertwining ρ ρ' N f).toContinuousLinearMap
  isIntertwining' g := by
    obtain ⟨g',rfl⟩ := g.exists_rep
    apply (relInvariantsIntertwining ρ ρ' N f).isIntertwining'

end ContRepresentation

variable [TopologicalSpace R]
variable (N : Subgroup G) [N.Normal]
variable {π_G : TopRep R G} {π_H : TopRep R H}

namespace TopRep

/-- Taking `N`-invariants, for `N` a normal subgroup of `G`, as a functor from topological
representations of `G` to topological representations of the quotient `G ⧸ N`. -/
def relInvariantsFunctor : TopRep R G ⥤ TopRep R (G ⧸ N) where
  obj rep       := TopRep.of (rep.ρ.relInvariantsInfl N)
  map f         := TopRep.ofHom (relInvariantsIntertwining' _ _ N f.hom)

variable (R) in
/-- The inclusion of the `N`-invariants — viewed as a `G`-representation by restricting the
`G ⧸ N`-action along the quotient map — back into the original representation, as a natural
transformation to the identity functor. -/
@[simps] def inflι : (relInvariantsFunctor N ⋙ resFunctor (QuotientGroup.mk' N)) ⟶ 𝟭 (TopRep R G)
    where
  app _ := TopRep.ofHom {
    toFun := Subtype.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    isIntertwining' _ := rfl
  }
  naturality _ _ _ := rfl

end TopRep

variable [TopologicalSpace G]

/-- The quotient map `G → G ⧸ N` as a continuous group homomorphism. -/
def QuotientGroup.mk'' : G →ₜ* G ⧸ N where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := by tauto

@[simp] lemma QuotientGroup.coe_mk'' : ↑(mk'' N) = mk' N := rfl

variable [IsTopologicalGroup G]

noncomputable section
namespace ContinuousCohomology

/-- The inflation map `Hⁿ(G ⧸ N, π^N) ⟶ Hⁿ(G, π)` on continuous cohomology: restrict along the
quotient map `G → G ⧸ N` and then push forward along the inclusion of the `N`-invariants. -/
abbrev inflApp (n : ℕ) (π : TopRep R G) :
    (relInvariantsFunctor N ⋙ Functor R (G ⧸ N) n).obj π
    ⟶ (Functor R G n).obj ((𝟭 _).obj π) :=
  (resNatTrans R (QuotientGroup.mk'' N) n).app ((relInvariantsFunctor N).obj π)
  ≫ (Functor R G n).map ((inflι R N).app π)

/-- The components `inflApp N n` are natural in the representation: they intertwine the
functorial maps on continuous cohomology. -/
lemma inflApp_naturality (n : ℕ) {π₁ π₂ : TopRep R G} (f : π₁ ⟶ π₂) :
    (relInvariantsFunctor N ⋙ Functor R (G ⧸ N) n).map f ≫ inflApp N n π₂ =
      inflApp N n π₁ ≫ (Functor R G n).map f := by
  have h := (Functor R G n).congr_map ((inflι R N).naturality f)
  rw [Functor.map_comp, Functor.map_comp] at h
  refine ((resNatTrans R (QuotientGroup.mk'' N) n).naturality_assoc
    ((relInvariantsFunctor N).map f) _).trans ?_
  rw [Category.assoc]
  exact whisker_eq _ h

/-- The inflation maps `inflApp N n` assembled into a natural transformation
`Hⁿ(G ⧸ N, -^N) ⟶ Hⁿ(G, -)` on continuous cohomology. -/
noncomputable def inflNatTrans (n : ℕ) :
    relInvariantsFunctor N ⋙ Functor R (G ⧸ N) n ⟶ Functor R G n where
  app            := inflApp N n
  naturality _ _ f := by
    /-
    Note that the following proof is a lot quicker than `exact inflApp_naturality N n f`.
    -/
    have := inflApp_naturality N n f
    simpa only [Functor.id_obj] using this

end ContinuousCohomology
end
