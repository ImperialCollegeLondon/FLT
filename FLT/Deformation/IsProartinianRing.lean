import FLT.Deformation.Algebra.InverseLimit.Basic
import FLT.Deformation.Algebra.InverseLimit.Topology
import FLT.Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib

open Topology TopologicalSpace
namespace Deformation

variable {A : Type*} [CommRing A]

variable (A) in
def ArtinianQuotientIdeal := {a : Ideal A // IsArtinianRing (A ⧸ a)}

instance : Coe (ArtinianQuotientIdeal A) (Ideal A) where
  coe a := a.1

instance : Preorder (ArtinianQuotientIdeal A) where
  le a b := (b : Ideal A) ≤ (a : Ideal A)
  le_refl := by simp
  le_trans := by
    rintro a b c hab hbc
    simp_all
    exact le_trans hbc hab

variable {a b : ArtinianQuotientIdeal A}

variable (a) in
abbrev proartinianCompletion_obj := A ⧸ (a : Ideal A)

instance : TopologicalSpace (proartinianCompletion_obj a) := ⊥

instance : DiscreteTopology (proartinianCompletion_obj a) where
  eq_bot := rfl

def ideal_le_of_artinianQuotientIdeal_le (h : a ≤ b) : (b : Ideal A) ≤ (a : Ideal A) := by
  simp [LE.le] at h
  exact h

def proartinianCompletion_map (h : a ≤ b)
    : (proartinianCompletion_obj b) →+* (proartinianCompletion_obj a) :=
  Ideal.ringHomOfQuot_of_le (ideal_le_of_artinianQuotientIdeal_le h)

variable (A) in
abbrev proartinianCompletion :=
  Ring.InverseLimit
    (fun (a : ArtinianQuotientIdeal A) => proartinianCompletion_obj a)
    proartinianCompletion_map

variable (A) in
noncomputable def diagonalMap : A →+* proartinianCompletion A :=
  Ring.InverseLimit.map_of_maps'
    proartinianCompletion_map
    (fun a ↦ Ideal.Quotient.mk (a : Ideal A))
    (by
      rintro a b h
      unfold proartinianCompletion_map
      aesop
    )

variable (a) in
def diagonalMap_toComponent : A →+* proartinianCompletion_obj a := algebraMap _ _

variable (A) in
class IsProartinianRing : Prop where
  pro_artin : Function.Bijective (diagonalMap A)

namespace IsProartinianRing

instance [IsProartinianRing A] : TopologicalSpace A := induced (diagonalMap A) (by infer_instance)

variable [IsProartinianRing A]

variable (A) in
instance instIsInducing : IsInducing (diagonalMap A) where
  eq_induced := rfl

instance : IsTopologicalRing A where
  continuous_add := (IsInducing.continuousAdd (diagonalMap A) (instIsInducing A)).continuous_add
  continuous_mul := (IsInducing.continuousMul (diagonalMap A) (instIsInducing A)).continuous_mul
  continuous_neg := (IsInducing.continuousNeg (f := diagonalMap A) (instIsInducing A) (by simp)).continuous_neg

instance [IsProartinianRing A] (I : Ideal A) : IsProartinianRing (A ⧸ I) where
  pro_artin := by
    simp [Function.Bijective, Function.Injective, Function.Surjective]
    split_ands
    . intro a b h
      sorry
    . intro b
      sorry

section Noetherian -- Proposition 2.4 of Smit&Lenstra

variable {𝓞 : Type*} [CommRing 𝓞] [IsNoetherianRing 𝓞] [IsLocalRing 𝓞]

variable [IsLocalRing A] [Algebra 𝓞 A] [IsNoetherianRing A] [IsProartinianRing A]

variable (A) in
instance noetherian_topology :
  IsAdic (IsLocalRing.maximalIdeal A) := sorry

variable (A) in
instance noetherian_isAdic :
  IsAdicComplete (IsLocalRing.maximalIdeal A) A := sorry

variable {A' : Type*} [CommRing A'] [Algebra 𝓞 A'] [IsLocalRing A'] [IsProartinianRing A']

variable (A A') in
lemma noetherian_continuous (f : A →ₐ[𝓞] A') : Continuous f := sorry

end Noetherian

end IsProartinianRing

end Deformation
