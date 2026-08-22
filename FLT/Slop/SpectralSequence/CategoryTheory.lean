/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.SpectralSequence.FilteredComplex
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The categorical spectral sequence of a filtered complex

This file packages the concrete pages of a `FilteredComplex` as mathlib's
`CategoryTheory.CohomologicalSpectralSequence` in `ModuleCat`.

At page `r`, the object in bidegree `(p, q)` is
`FilteredComplex.pageBigraded r p q`, and the differential has bidegree
`(r, 1 - r)`.  The successor isomorphism is obtained by comparing the
categorical homology of the page complex with the explicit quotient
`ker dᵣ / range dᵣ`, then applying `FilteredComplex.pageSuccEquiv`.
-/

@[expose] public section

open CategoryTheory
open Submodule LinearMap

universe u v

namespace FilteredComplex

variable {R : Type u} [Ring R] (K : FilteredComplex.{u, v} R)

/-- The differential on the categorical `r`-page.  It is the concrete page
differential when the two bidegrees differ by `(r, 1 - r)`, and zero otherwise. -/
def pageDifferential (r : ℤ) (a b : ℤ × ℤ) :
    K.pageBigraded r a.1 a.2 →ₗ[R] K.pageBigraded r b.1 b.2 :=
  if h : a + (⟨r, 1 - r⟩ : ℤ × ℤ) = b then
    K.dPageAux r a.1 b.1 (a.1 + a.2) (b.1 + b.2)
      (by
        have h1 := congrArg Prod.fst h
        simpa using h1.symm)
      (by
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        dsimp at h1 h2
        omega)
  else 0

/-- If two bidegrees differ by `(r, 1 - r)`, `pageDifferential` is the
corresponding concrete page differential. -/
@[simp]
lemma pageDifferential_of_rel (r : ℤ) (a b : ℤ × ℤ)
    (h : a + (⟨r, 1 - r⟩ : ℤ × ℤ) = b) :
    pageDifferential K r a b =
      K.dPageAux r a.1 b.1 (a.1 + a.2) (b.1 + b.2)
        (by
          have h1 := congrArg Prod.fst h
          simpa using h1.symm)
        (by
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          dsimp at h1 h2
          omega) := by
  simp only [pageDifferential, dif_pos h]

/-- The `r`-page of a filtered complex as a homological complex in `ModuleCat`.
Its objects are the bigraded pages and its complex shape has step `(r, 1 - r)`. -/
def pageComplex (r : ℤ) :
    HomologicalComplex (ModuleCat.{v} R)
      (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) where
  X a := ModuleCat.of R (K.pageBigraded r a.1 a.2)
  d a b := ModuleCat.ofHom (pageDifferential K r a b)
  shape a b h := by
    change ¬a + (⟨r, 1 - r⟩ : ℤ × ℤ) = b at h
    apply ModuleCat.hom_ext
    simp [pageDifferential, h]
  d_comp_d' a b c hab hbc := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
    rw [pageDifferential_of_rel K r a b hab]
    rw [pageDifferential_of_rel K r b c hbc]
    apply K.dPageAux_comp

/-- The object of `pageComplex` at `(p, q)` is the concrete bigraded page
`Eᵣ^{p,q}`. -/
@[simp]
lemma pageComplex_X (r : ℤ) (a : ℤ × ℤ) :
    (K.pageComplex r).X a = ModuleCat.of R (K.pageBigraded r a.1 a.2) := rfl

/-- On a pair of related bidegrees, the underlying linear map of the
categorical page differential is `FilteredComplex.dPageAux`. -/
@[simp]
lemma pageComplex_d_hom_of_rel (r : ℤ) (a b : ℤ × ℤ)
    (h : a + (⟨r, 1 - r⟩ : ℤ × ℤ) = b) :
    ((K.pageComplex r).d a b).hom =
      K.dPageAux r a.1 b.1 (a.1 + a.2) (b.1 + b.2)
        (by
          have h1 := congrArg Prod.fst h
          simpa using h1.symm)
        (by
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          dsimp at h1 h2
          omega) := by
  simp [pageComplex, pageDifferential, h]

/-! ## Functoriality of the categorical pages -/

section Functoriality

variable {K K' K'' : FilteredComplex.{u, v} R}

/-- The morphism of categorical `r`-pages induced by a morphism of filtered
cochain complexes. -/
def Hom.pageHom (f : K ⟶ K') (r : ℤ) : K.pageComplex r ⟶ K'.pageComplex r where
  f a := ModuleCat.ofHom (f.mapPage r a.1 (a.1 + a.2))
  comm' a b hab := by
    have hp : b.1 = a.1 + r := by
      have h := congrArg Prod.fst hab
      simpa using h.symm
    have hn : b.1 + b.2 = a.1 + a.2 + 1 := by
      have h1 := congrArg Prod.fst hab
      have h2 := congrArg Prod.snd hab
      dsimp at h1 h2
      omega
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp]
    rw [K.pageComplex_d_hom_of_rel r a b hab]
    rw [K'.pageComplex_d_hom_of_rel r a b hab]
    exact (f.mapPage_dPageAux r a.1 b.1 (a.1 + a.2) (b.1 + b.2) hp hn).symm

@[simp] lemma Hom.pageHom_f (f : K ⟶ K') (r : ℤ) (a : ℤ × ℤ) :
    (f.pageHom r).f a = ModuleCat.ofHom (f.mapPage r a.1 (a.1 + a.2)) := rfl

@[simp] lemma Hom.pageHom_id (K : FilteredComplex.{u, v} R) (r : ℤ) :
    Hom.pageHom (𝟙 K) r = 𝟙 (K.pageComplex r) := by
  ext a
  simp

@[simp] lemma Hom.pageHom_comp (f : K ⟶ K') (g : K' ⟶ K'') (r : ℤ) :
    (f ≫ g).pageHom r = f.pageHom r ≫ g.pageHom r := by
  ext a
  simp

/-- The functor sending a filtered complex to its categorical `r`-page. -/
@[simps]
def pageComplexFunctor (R : Type u) [Ring R] (r : ℤ) :
    FilteredComplex.{u, v} R ⥤
      HomologicalComplex (ModuleCat.{v} R)
        (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) where
  obj K := K.pageComplex r
  map f := f.pageHom r

end Functoriality

/-- The categorical homology of the `r`-page at a bidegree is isomorphic to the
corresponding object of the `(r + 1)`-page. -/
noncomputable def pageHomologyIso (r : ℤ) (b : ℤ × ℤ) :
    (K.pageComplex r).homology b ≅ (K.pageComplex (r + 1)).X b := by
  let a : ℤ × ℤ := (b.1 - r, b.2 + r - 1)
  let c : ℤ × ℤ := (b.1 + r, b.2 + 1 - r)
  let shape := ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)
  have hab : shape.Rel a b := by
    change a + (⟨r, 1 - r⟩ : ℤ × ℤ) = b
    apply Prod.ext
    · dsimp [a]
      omega
    · dsimp [a]
      omega
  have hbc : shape.Rel b c := by
    change b + (⟨r, 1 - r⟩ : ℤ × ℤ) = c
    apply Prod.ext
    · rfl
    · dsimp [c]
      omega
  have hpin : a.1 = b.1 - r := by simp [a]
  have hpout : c.1 = b.1 + r := by simp [c]
  have hnin : a.1 + a.2 = b.1 + b.2 - 1 := by dsimp [a]; omega
  have hnout : c.1 + c.2 = b.1 + b.2 + 1 := by dsimp [c]; omega
  have pageSuccEquivAux
      (p pin pout n nin nout : ℤ)
      (hpin' : pin = p - r) (hpout' : pout = p + r)
      (hnin' : nin = n - 1) (hnout' : nout = n + 1) :
      K.page (r + 1) p n ≃ₗ[R]
        (↥(ker (K.dPageAux r p pout n nout hpout' hnout')) ⧸
          (range (K.dPageAux r pin p nin n
            (by rw [hpin']; ring) (by rw [hnin']; ring))).comap
            (ker (K.dPageAux r p pout n nout hpout' hnout')).subtype) := by
    subst hpin'
    subst hpout'
    subst hnin'
    subst hnout'
    exact K.pageSuccEquiv r p n
  let S := (K.pageComplex r).sc' a b c
  refine (K.pageComplex r).homologyIsoSc' a b c
      (shape.prev_eq' hab) (shape.next_eq' hbc) ≪≫
    S.moduleCatHomologyIso ≪≫ ?_
  refine eqToIso ?_ ≪≫
    (pageSuccEquivAux b.1 a.1 c.1 (b.1 + b.2) (a.1 + a.2) (c.1 + c.2)
      hpin hpout hnin hnout).symm.toModuleIso
  change ModuleCat.of R
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) =
    ModuleCat.of R
      (↥(ker (K.dPageAux r b.1 c.1 (b.1 + b.2) (c.1 + c.2) hpout hnout)) ⧸
        (range (K.dPageAux r a.1 b.1 (a.1 + a.2) (b.1 + b.2)
          (by rw [hpin]; ring) (by rw [hnin]; ring))).comap
          (ker (K.dPageAux r b.1 c.1 (b.1 + b.2) (c.1 + c.2) hpout hnout)).subtype)
  rw [LinearMap.range_codRestrict]
  change ModuleCat.of R
      (↥(LinearMap.ker ((K.pageComplex r).d b c).hom) ⧸
        (LinearMap.range ((K.pageComplex r).d a b).hom).comap
          (LinearMap.ker ((K.pageComplex r).d b c).hom).subtype) = _
  rw [K.pageComplex_d_hom_of_rel r a b hab]
  rw [K.pageComplex_d_hom_of_rel r b c hbc]
  congr 4

/-- The cohomological spectral sequence associated to a filtered complex, in
mathlib's categorical `SpectralSequence` API, starting at page `r₀`. -/
noncomputable def toCohomologicalSpectralSequence (r₀ : ℤ) :
    CategoryTheory.CohomologicalSpectralSequence (ModuleCat.{v} R) r₀ where
  page r _ := K.pageComplex r
  iso r r' b hrr' _ := by
    subst hrr'
    exact K.pageHomologyIso r b

end FilteredComplex
