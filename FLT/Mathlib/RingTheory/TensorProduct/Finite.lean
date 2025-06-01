import Mathlib.RingTheory.TensorProduct.Finite


open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance (R A M : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [CommSemiring M]
    [Algebra R M] [Module.Finite R M] : Module.Finite A (M ⊗[R] A) :=
  Module.Finite.of_equiv_equiv (RingEquiv.refl A) (Algebra.TensorProduct.comm R A M).toRingEquiv rfl
-- Module.Finite.of_equiv_equiv uses rings so we can't use semirings in the above proof?

-- variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [Semiring M]
--     [Algebra R M] [h : Module.Finite R M] in
-- attribute [local instance] Algebra.TensorProduct.rightAlgebra in
-- /-- If M is a finite R-module then M ⊗[R] A is a finite A-module. -/
-- instance _root_.Module.Finite.base_change_right :
--     Module.Finite A (M ⊗[R] A) := by
--   classical
--     obtain ⟨s, hs⟩ := h.fg_top
--     refine ⟨⟨s.image ((TensorProduct.mk R M A).flip 1), eq_top_iff.mpr ?_⟩⟩
--     rintro x -
--     induction x with
--     | zero => exact zero_mem _
--     | tmul x y =>
--       have : x ⊗ₜ[R] y = y • x ⊗ₜ[R] 1 := by simp [RingHom.smul_toAlgebra']
--       rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs,
--         Submodule.map_top, LinearMap.range_coe, this]
--       exact Submodule.smul_mem _ y (Submodule.subset_span <| Set.mem_range_self x)
--     | add x y hx hy => exact Submodule.add_mem _ hx hy
