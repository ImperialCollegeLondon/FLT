/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Basic

Material destined for Mathlib.
-/

@[expose] public section

-- TODO upstream
namespace Rat

open NumberField

lemma infinitePlace_isReal (v : InfinitePlace ℚ) : v.IsReal :=
  Subsingleton.elim v infinitePlace ▸ isReal_infinitePlace

end Rat
