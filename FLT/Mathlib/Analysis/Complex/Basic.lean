import Mathlib.Analysis.Complex.Basic

open Complex

variable {s t : Set ℝ}

lemma IsCompact.reProdIm (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ×ℂ t) :=
  equivRealProdCLM.toHomeomorph.isCompact_preimage.2 (hs.prod ht)
