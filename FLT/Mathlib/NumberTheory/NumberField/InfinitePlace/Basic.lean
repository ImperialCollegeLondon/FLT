import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

-- TODO upstream
namespace Rat

open NumberField

lemma infinitePlace_isReal (v : InfinitePlace ℚ) : v.IsReal :=
  Subsingleton.elim v infinitePlace ▸ isReal_infinitePlace

end Rat
