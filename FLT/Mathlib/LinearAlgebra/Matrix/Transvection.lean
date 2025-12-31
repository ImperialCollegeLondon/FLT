import Mathlib.LinearAlgebra.Matrix.Transvection
/-!

Variant of `Matrix.diagonal_transvection_induction_of_det_ne_zero`
that works over a commutative ring. Note that we have to *assume*
that the matrix is a product of transvections and a diagonal matrix;
this is not true in general (I believe; I think there's some obstruction
in algebraic K₂?)

-/
