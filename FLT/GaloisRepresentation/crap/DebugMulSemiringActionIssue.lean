/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
-- import FLT.Deformations.RepresentationTheory.Basic -- fails
-- import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup works
-- import FLT.Deformations.RepresentationTheory.Etale -- works
--import Mathlib
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.FinitePlaces
--import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup -- mathlib imports above?
import FLT.Deformations.RepresentationTheory.Frobenius
import FLT.Deformations.RepresentationTheory.IntegralClosure
import FLT.NumberField.Completion.Finite
--import FLT.Deformations.RepresentationTheory.Etale -- only for mathlib imports?

import FLT.Deformations.RepresentationTheory.IntegralClosure -- for integral closure notation

--import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
--import FLT.Deformations.RepresentationTheory.Etale

open NumberField

universe uK

variable {K : Type uK} {L : Type*} [Field K] [Field L]
variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {B : Type*} [CommRing B] [TopologicalSpace B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {n : Type*} [Fintype n] [DecidableEq n]

variable [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v

#synth MulSemiringAction (Γ Kᵥ) (IntegralClosure (↥𝒪ᵥ) (Kᵥᵃˡᵍ))
