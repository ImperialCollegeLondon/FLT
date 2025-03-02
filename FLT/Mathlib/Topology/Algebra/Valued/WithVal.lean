import Mathlib.Topology.Algebra.Valued.WithVal

variable {A K L B Γ₀ : Type*} [Ring L] [CommRing K] [LinearOrderedCommGroupWithZero Γ₀]
  [Semiring A] [Module A K] [Module A L] [Semiring B] [Module A B] [Module B L]
  (v : Valuation K Γ₀) (w : Valuation L Γ₀)

instance [Algebra K L]  : Algebra (WithVal v) L := ‹Algebra K L›

instance [Algebra K L] : Algebra K (WithVal w) := ‹Algebra K L›

instance [Algebra K L] [IsScalarTower A K L] : IsScalarTower A (WithVal v) L :=
  ‹IsScalarTower A K L›

instance [IsScalarTower A B L] : IsScalarTower A B (WithVal w) :=
  ‹IsScalarTower A B L›
