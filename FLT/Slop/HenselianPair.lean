/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.HenselianPair.Coprime
public import FLT.Slop.HenselianPair.Defs
public import FLT.Slop.HenselianPair.HenselianRing
public import FLT.Slop.HenselianPair.Idempotents
public import FLT.Slop.HenselianPair.Polynomial
public import FLT.Slop.HenselianPair.Quotient

/-!
# Henselian pairs

A pair `(R, I)` is a *Henselian pair* if `I` is contained in the Jacobson radical of `R` and every
monic polynomial whose reduction modulo `I` factors into coprime monic factors lifts to a matching
factorisation over `R`.  This is the coprime-factorisation definition of Stacks Tag 09XE.

This file re-exports the development.

## Contents

* `FLT.Slop.HenselianPair.Coprime` — coprimality of monic polynomials descends along
  Jacobson-radical quotients.
* `FLT.Slop.HenselianPair.Polynomial` — polynomial helpers; uniqueness of simple-root
  lifts from `I ≤ Jac(R)` alone.
* `FLT.Slop.HenselianPair.HenselianRing` — uniqueness of root lifts for `HenselianRing`.
* `FLT.Slop.HenselianPair.Defs` — `IsHenselianPair` and the bridge to `HenselianRing`.
* `FLT.Slop.HenselianPair.Idempotents` — lifting idempotents (Stacks Tag 09XI(2)).
* `FLT.Slop.HenselianPair.Quotient` — quotient and subideal stability.

## References

* [Stacks Project, Tag 09XE](https://stacks.math.columbia.edu/tag/09XE)
-/
