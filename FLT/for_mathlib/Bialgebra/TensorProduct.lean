/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Yanqiao Zhou, Jujian Zhang
-/

import FLT.for_mathlib.Coalgebra.TensorProduct
import Mathlib.RingTheory.Bialgebra

open TensorProduct

namespace Bialgebra

variable (R A B : Type*) [CommSemiring R]
variable [Semiring A] [Bialgebra R A]
variable [Semiring B] [Bialgebra R B]

noncomputable instance : Bialgebra R (A ⊗[R] B) where
  counit_one := sorry
  mul_compr₂_counit := sorry
  comul_one := sorry
  mul_compr₂_comul := sorry

end Bialgebra
