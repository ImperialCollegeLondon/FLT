import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Module.Prod

/-
I am not fully convinced what the naming should be for this instance, or if this is where it belongs
as it conflicts with Prod.instModule ... also will there be a diamond when S = R?
-/
namespace ModuleProd

variable {R S M N : Type*}

/-- The (R × S)-module structure on (M × N). -/
local instance instModuleProd [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module S N] : Module (R × S) (M × N) where
  smul rs mn := (rs.1 • mn.1, rs.2 • mn.2)
  one_smul mn := by cases mn; ext; exacts [one_smul R _, one_smul S _]
  mul_smul rs rs' mn := by
    cases rs; cases rs'; cases mn
    ext <;>
    exact mul_smul _ _ _
  smul_zero rs := by cases rs; ext <;> exact smul_zero _
  smul_add rs mn mn' := by
    cases rs; cases mn; cases mn'
    ext <;>
    exact smul_add _ _ _
  add_smul rs rs' mn := by
    cases rs; cases rs'; cases mn
    ext <;>
    exact add_smul _ _ _
  zero_smul mn := by cases mn; ext <;> exact zero_smul _ _

/-- Product map of the scalar multiplications defined on the product `R × M` and `S × N`. -/
def smul [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module S N] : (R × M) × (S × N) → (M × N) :=
  Prod.map (fun (r, m) => r • m) (fun (s, n) => s • n)

end ModuleProd
