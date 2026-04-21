module

public import Mathlib.LinearAlgebra.Matrix.Transvection
/-!

Variant of `Matrix.diagonal_transvection_induction_of_det_ne_zero`
that works over a commutative ring. Note that we have to *assume*
that the matrix is a product of transvections and a diagonal matrix;
this is not true in general (I believe; I think there's some obstruction
in SK₁(R), the kernel of det:K₁(R) → Rˣ)

-/

@[expose] public section

open Matrix TransvectionStruct

namespace Matrix

/-- The claim that a matrix is a product of transvections, a diagonal matrix, and more
transvections. Always true if the base ring is a field. -/
def Pivot.ExistsListTransvecMulDiagonalMulListTransvec {n : Type*} {R : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (M : Matrix n n R) : Prop :=
  ∃ (L L' : List (TransvectionStruct n R)) (D : n → R),
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod

lemma Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec' {n : Type*} {𝕜 : Type*} [Field 𝕜]
    [DecidableEq n] [Fintype n] (M : Matrix n n 𝕜) :
    Pivot.ExistsListTransvecMulDiagonalMulListTransvec M :=
  Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M

section TransvectionStruct_dot_map

variable {n : Type*} {R S : Type*} [CommRing R] [CommRing S]
    [DecidableEq n] (f : R →+* S)

/-- Base change of a TransvectionStruct along a ring homomorphism. -/
def TransvectionStruct.map {n : Type*} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : TransvectionStruct n R) :
    TransvectionStruct n S where
  i := t.i
  j := t.j
  hij := t.hij
  c := f t.c

lemma TransvectionStruct.toMatrix_map [Fintype n] (t : TransvectionStruct n R) :
    (toMatrix ∘ TransvectionStruct.map f) t = f.mapMatrix t.toMatrix := by
  simp [map, transvection, toMatrix, map_add]

@[simp]
lemma TransvectionStruct.map_toMatrix [Finite n] (t : TransvectionStruct n R) :
    (TransvectionStruct.map f t).toMatrix = t.toMatrix.map f :=
  let := Fintype.ofFinite n
  t.toMatrix_map f

lemma TransvectionStruct.mapMatrix_map_toMatrix_prod [Fintype n]
    (L : List (TransvectionStruct n R)) :
    f.mapMatrix (List.map toMatrix L).prod =
    (List.map (toMatrix ∘ TransvectionStruct.map f) L).prod := by
  rw [map_list_prod]
  congr 1
  simp

@[simp]
lemma TransvectionStruct.mapMatrix_map_toMatrix_prod' [Fintype n]
    (L : List (TransvectionStruct n R)) :
    (List.map toMatrix L).prod.map ⇑f =
    (List.map (toMatrix ∘ TransvectionStruct.map f) L).prod :=
  TransvectionStruct.mapMatrix_map_toMatrix_prod f L

end TransvectionStruct_dot_map

lemma Pivot.baseChange_existsListTransvecEtc {n : Type*} {R : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (M : Matrix n n R)
    (hM : Pivot.ExistsListTransvecMulDiagonalMulListTransvec M)
    (S : Type*) [CommRing S] (f : R →+* S) :
    Pivot.ExistsListTransvecMulDiagonalMulListTransvec (f.mapMatrix M) := by
  obtain ⟨L, L', D, rfl⟩ := hM
  exact ⟨L.map (TransvectionStruct.map f), L'.map (TransvectionStruct.map f),
    fun i ↦ f (D i), by simp⟩

open Pivot

variable {n : Type*} {R : Type*} [CommRing R] [DecidableEq n] [Fintype n]

-- this proof is literally cut and pasted from mathlib
/-- Variant of `Matrix.diagonal_transvection_induction` for commutative rings
under the extra assumption `ExistsListTransvecMulDiagonalMulListTransvec M`
(which is automatic for matrices over fields). -/
theorem diagonal_transvection_induction' (P : Matrix n n R → Prop) (M : Matrix n n R)
    (hM : ExistsListTransvecMulDiagonalMulListTransvec M)
    (hdiag : ∀ D : n → R, det (diagonal D) = det M → P (diagonal D))
    (htransvec : ∀ t : TransvectionStruct n R, P t.toMatrix) (hmul : ∀ A B, P A → P B → P (A * B)) :
    P M := by
  rcases hM with ⟨L, L', D, h⟩
  have PD : P (diagonal D) := hdiag D (by simp [h])
  suffices H :
    ∀ (L₁ L₂ : List (TransvectionStruct n R)) (E : Matrix n n R),
      P E → P ((L₁.map toMatrix).prod * E * (L₂.map toMatrix).prod) by
    rw [h]
    apply H L L'
    exact PD
  intro L₁ L₂ E PE
  induction L₁ with
  | nil =>
    simp only [Matrix.one_mul, List.prod_nil, List.map]
    induction L₂ generalizing E with
    | nil => simpa
    | cons t L₂ IH =>
      simp only [← Matrix.mul_assoc, List.prod_cons, List.map]
      apply IH
      exact hmul _ _ PE (htransvec _)
  | cons t L₁ IH =>
    simp only [Matrix.mul_assoc, List.prod_cons, List.map] at IH ⊢
    exact hmul _ _ (htransvec _) IH

-- this proof is literally cut and pasted from mathlib with `≠ 0` changed to `IsUnit`
-- and 𝕜 changed to R and addition of `(hM : ExistsListTransvecMulDiagonalMulListTransvec M)`
theorem diagonal_transvection_induction_of_det_unit (P : Matrix n n R → Prop) (M : Matrix n n R)
    (hM : ExistsListTransvecMulDiagonalMulListTransvec M)
    (hMdet : IsUnit (det M)) (hdiag : ∀ D : n → R, IsUnit (det (diagonal D)) → P (diagonal D))
    (htransvec : ∀ t : TransvectionStruct n R, P t.toMatrix)
    (hmul : ∀ A B, IsUnit (det A) → IsUnit (det B) → P A → P B → P (A * B)) : P M := by
  let Q : Matrix n n R → Prop := fun N => IsUnit (det N) ∧ P N
  have : Q M := by
    apply diagonal_transvection_induction' Q M hM
    · grind
    · intro t
      exact ⟨by simp, htransvec t⟩
    · intro A B QA QB
      exact ⟨by simp [QA.1, QB.1], hmul A B QA.1 QB.1 QA.2 QB.2⟩
  exact this.2

end Matrix
