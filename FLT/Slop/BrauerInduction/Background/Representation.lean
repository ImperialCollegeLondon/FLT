/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants

public import Mathlib.RepresentationTheory.Character

@[expose] public section

universe u v w w'

/-!
# Auxiliary facts about bundled representations

This file develops character-theoretic and invariant-subspace lemmas for
`Representation k G V`.

Main contents:

* `Representation.character`;
* character formulas for products, tensor products, duals, internal Homs,
  and finite direct sums;
* invariant submodules and the averaging idempotent for finite groups;
* a trace formula for the multiplicity of invariants;
* universe-lifted representations.
-/

section Helper

variable {k : Type*} [CommSemiring k]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable [(i : ι) → AddCommGroup (V i)]
variable [(i : ι) → Module k (V i)]
variable [(i : ι) → Module.Free k (V i)]
variable [(i : ι) → Module.Finite k (V i)]

lemma LinearMap.trace_pi_diag (f : ∀ i, V i →ₗ[k] V i) :
    LinearMap.trace k ((i : ι) → V i)
        (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i)
      =
    ∑ i, LinearMap.trace k (V i) (f i) := by
  classical
  set M' := LinearMap.pi (fun i => f i ∘ₗ LinearMap.proj i)
  convert LinearMap.trace_eq_matrix_trace k
    (Pi.basis fun i => Module.Free.chooseBasis k (V i)) M' using 1
  rw [Finset.sum_congr rfl fun i _ =>
    LinearMap.trace_eq_matrix_trace k
      (Module.Free.chooseBasis k (V i)) (f i)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Pi.basis_apply, Pi.basis_repr]
  rw [Finset.sum_sigma']
  simp_all only [Finset.univ_sigma_univ, pi_apply, coe_comp, coe_proj, Function.comp_apply,
    Function.eval, Pi.single_eq_same, M']

private lemma conj_lmap_eq (f : ∀ i, V i →ₗ[k] V i) :
    (DirectSum.linearEquivFunOnFintype k ι V).conj (DirectSum.lmap f) =
    LinearMap.pi (fun i =>
      (f i).comp (LinearMap.proj i)) := by
  exact (Module.dualMap_dualMap_eq_iff k ((i : ι) → V i)).mp rfl

section CommRing

variable {k : Type*} [CommRing k]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable [(i : ι) → AddCommGroup (V i)]
variable [(i : ι) → Module k (V i)]
variable [(i : ι) → Module.Free k (V i)]
variable [(i : ι) → Module.Finite k (V i)]

open DirectSum in
lemma DirectSum.trace_lmap (f : ∀ i, V i →ₗ[k] V i) :
    LinearMap.trace k (⨁ i, V i) (DirectSum.lmap f)
      = ∑ i, LinearMap.trace k (V i) (f i) := by
  rw [← LinearMap.trace_conj' (DirectSum.lmap f) (DirectSum.linearEquivFunOnFintype k ι V)]
  rw [conj_lmap_eq]
  exact LinearMap.trace_pi_diag f

end CommRing

section Group

variable {G k V W : Type*} [Group G] [CommSemiring k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [Module.Finite k V] [Module.Finite k W] [Module.Free k V]
    (ρ : Representation k G V) (σ : Representation k G W)

/-- dualTensorHom as an equivalence of representations. -/
@[simps!]
noncomputable def Representation.Equiv.dualTensorHomOfFiniteFree :
    Equiv (tprod ρ.dual σ) (linHom ρ σ) where
  toLinearEquiv := dualTensorHomEquiv (R := k) (M := V) (N := W)
  isIntertwining' g := by
    ext v' w v; simp [Module.Dual.transpose_apply]

end Group

end Helper

namespace Representation

variable {G k : Type*} [Monoid G] [Field k]

variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

lemma character_def (ρ : Representation k G V) (g : G) :
  character ρ g = LinearMap.trace k V (ρ g) := rfl

/-- Equivalent representations have the same character. -/
lemma char_equiv
    {ρ : Representation k G V} {σ : Representation k G W}
     (h : Representation.Equiv ρ σ) (g : G) :
    ρ.character g = σ.character g := by
  simp only [character]
  have h_conj : h.toLinearEquiv.conj (ρ g) = σ g := by
    ext v
    change h (ρ g (h.symm v)) = σ g v
    have h' := LinearMap.congr_fun (h.isIntertwining' g) (h.symm v)
    simpa using h'
  rw [← h_conj]
  exact Eq.symm (LinearMap.trace_conj' (ρ g) h.toLinearEquiv)


/-- The character of a product representation is the sum of the characters of
  the two factors. -/
@[simp]
lemma char_prod [Module.Finite k V] [Module.Finite k W]
  (ρ : Representation k G V) (σ : Representation k G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  ext g
  dsimp[Representation.prod]
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

section directSum

variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable [(i : ι) → AddCommGroup (V i)]
variable [(i : ι) → Module k (V i)]
variable [(i : ι) → Module.Free k (V i)]
variable [(i : ι) → Module.Finite k (V i)]

open DirectSum

/-- The character of a finite direct sum of representations is the sum of the
  characters of the summands. -/
@[simp]
lemma char_directSum (ρ : (i : ι) → Representation k G (V i)) (g : G) :
    (Representation.directSum ρ).character g = ∑ i, (ρ i).character g := by
  dsimp[character]
  exact DirectSum.trace_lmap fun x ↦ (ρ x) g

end directSum

section numOfFixedPoints

variable {k G : Type*} [Monoid G] [CommRing k]

open Classical in
/-- For the representation of finitely supported functions on a finite `G`-set,
    the trace of the linear map attached to `g : G` is the number of fixed points of `g`. -/
lemma ofMulAction_trace
    {X : Type*} [Finite X] [MulAction G X] (g : G) :
    LinearMap.trace k (MonoidAlgebra k X) (Representation.ofMulAction k G X g)
    = (Nat.card {x : X // g • x = x} : k) := by
  letI : Fintype X := Fintype.ofFinite X
  let b := MonoidAlgebra.basis X k
  have hrepr : ∀ w : MonoidAlgebra k X, b.repr w = w.coeff := fun _ => rfl
  rw [LinearMap.trace_eq_matrix_trace k b]
  rw [Matrix.trace]
  trans ∑ x : X, if g • x = x then (1 : k) else 0
  · apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply, hrepr,
      ofMulAction_single, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]

end numOfFixedPoints

namespace GroupAlgebra

open scoped MonoidAlgebra

-- Ported from Mathlib.RepresentationTheory.Invariants

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable def average (k : Type u) (G : Type v) [Field k] [Monoid G] [Fintype G] : k[G] :=
   ((Fintype.card G : k)⁻¹) • ∑ g : G, MonoidAlgebra.of k G g

@[simp]
theorem mul_average_left (g : G) :
    MonoidAlgebra.single g 1 * average k G = average k G := by
  simp only [mul_one, Finset.mul_sum, Algebra.mul_smul_comm, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G → k[G] := fun x => MonoidAlgebra.single x 1
  change ((Fintype.card G : k)⁻¹) • ∑ x : G, f (g * x) = ((Fintype.card G : k)⁻¹) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

@[simp]
theorem mul_average_right (g : G) :
    average k G * MonoidAlgebra.single g 1 = average k G :=  by
  simp only [mul_one, Finset.sum_mul, Algebra.smul_mul_assoc, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G → k[G] := fun x => MonoidAlgebra.single x 1
  change ((Fintype.card G : k)⁻¹) • ∑ x : G, f (x * g) = ((Fintype.card G : k)⁻¹)  • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) _]

/-- The action of `average k G` gives a projection map onto the subspace of invariants.
-/
noncomputable def averageMap (ρ : Representation k G V) : V →ₗ[k] V :=
  asAlgebraHom ρ (average k G)

/-- The `averageMap` sends elements of `V` to the subspace of invariants.
-/
theorem averageMap_invariant (ρ : Representation k G V) (v : V) :
    averageMap ρ v ∈ invariants ρ := fun g => by
  rw [averageMap, ← asAlgebraHom_single_one, ← Module.End.mul_apply,
    ← map_mul (asAlgebraHom ρ), mul_average_left]

/--
In characteristic zero, the averaging operator acts as the identity on invariant
vectors.
-/
theorem averageMap_id [CharZero k]
    (ρ : Representation k G V) (v : V) (hv : v ∈ invariants ρ) :
    averageMap ρ v = v := by
  rw [mem_invariants] at hv
  have hcard : (Fintype.card G : k) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [averageMap, average, map_sum, hv, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul k (Fintype.card G) v, smul_smul, hcard]

theorem isProj_averageMap [CharZero k] (ρ : Representation k G V) :
    LinearMap.IsProj ρ.invariants (averageMap ρ) := ⟨averageMap_invariant ρ, averageMap_id ρ⟩

end GroupAlgebra

theorem average_char_eq_finrank_invariants
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    [Fintype G] [CharZero k]
    {V : Type w} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) :
    ((Fintype.card G : k)⁻¹) * (∑ g : G, ρ.character g)
      =
    (Module.finrank k (invariants ρ) : k) := by
  haveI : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  have h := (GroupAlgebra.isProj_averageMap ρ).trace
  rw [← h]
  change
    (Fintype.card G : k)⁻¹ * ∑ x : G, (LinearMap.trace k V) (ρ x) =
      (LinearMap.trace k V) (GroupAlgebra.averageMap ρ)
  rw [GroupAlgebra.averageMap, GroupAlgebra.average]
  simp only [MonoidAlgebra.of_apply, map_smul, map_sum, asAlgebraHom_single, one_smul, smul_eq_mul]

noncomputable def ulift
    {k : Type u} [Semiring k]
    {G : Type v} [Monoid G]
    {A : Type w} [AddCommMonoid A] [Module k A]
    (ρ : Representation k G A) :
    Representation k G (ULift.{w'} A) where
  toFun g :=
    { toFun := fun x => ULift.up (ρ g x.down)
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro g h
    ext x
    simp only [map_mul, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- The tautological linear equivalence between a representation space and its universe lift. -/
noncomputable def uliftLinearEquiv
    {k : Type u} [Semiring k]
    {G : Type v} [Monoid G]
    {V : Type w} [AddCommMonoid V] [Module k V]
    (_ : Representation k G V) :
    V ≃ₗ[k] ULift.{w'} V where
  toFun := fun x => ULift.up x
  invFun := fun x => x.down
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    cases x
    rfl
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl

@[simp]
lemma uliftLinearEquiv_apply
    {k : Type u} [Semiring k]
    {G : Type v} [Monoid G]
    {V : Type w} [AddCommMonoid V] [Module k V]
    (ρ : Representation k G V) (x : V) :
    ρ.uliftLinearEquiv x = ULift.up x :=
  rfl

@[simp]
lemma uliftLinearEquiv_symm_apply
    {k : Type u} [Semiring k]
    {G : Type v} [Monoid G]
    {V : Type w} [AddCommMonoid V] [Module k V]
    (ρ : Representation k G V) (x : ULift.{w'} V) :
    (ρ.uliftLinearEquiv).symm x = x.down :=
  rfl

@[simp]
lemma character_ulift
    {k : Type u} [Field k]
    {G : Type v} [Monoid G]
    {V : Type w} [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Module.Free k V]
    (ρ : Representation k G V) :
    ρ.ulift.character = ρ.character := by
  ext g
  change
    LinearMap.trace k (ULift V) (ρ.ulift g) =
      LinearMap.trace k V (ρ g)
  have hconj :
      (ρ.uliftLinearEquiv).conj (ρ g) = ρ.ulift g := by
    ext x
    rfl
  rw [← hconj]
  exact LinearMap.trace_conj' (ρ g) ρ.uliftLinearEquiv

end Representation
