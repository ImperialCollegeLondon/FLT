import Mathlib
import FLT.NumberField.Completion
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField InfinitePlace

open scoped Classical TensorProduct

noncomputable local instance : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _

-- see https://leanprover.zulipchat.com/#narrow/channel/416277-FLT/topic/Functoriality.20of.20infinite.20completion.20for.20number.20fields/near/492313867
/-- The canonical map from the infinite adeles of K to the infinite adeles of L -/
noncomputable def NumberField.InfiniteAdeleRing.baseChange :
    --  Π v, K_v → Π v, Π (w | w.comap = v), L_w → Π (v, ⟨w, w.comap =v⟩), L_w → Π w, L_w
    InfiniteAdeleRing K →A[K] InfiniteAdeleRing L :=
  -- Π (v, ⟨w, w.comap =v⟩), L_w → Π w, L_w
  (ContinuousAlgEquiv.piCongrLeft K _ (Equiv.sigmaFiberEquiv _)).toContinuousAlgHom.comp <|
    -- Π v, Π (w | w.comap = v), L_w → Π (v, ⟨w, w.comap =v⟩), L_w
    (ContinuousAlgEquiv.piCurry K _).symm.toContinuousAlgHom.comp
      -- Π v, K_v → Π v, Π (w | w.comap = v), L_w
      (Pi.mapContinuousAlgHom K _ _
        -- K_v → Π (w | w.comap = v), L_w
        (fun v : InfinitePlace K => (Completion.baseChange L v).restrictScalars K))

noncomputable instance : Algebra (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) :=
  Algebra.TensorProduct.rightAlgebra

instance : TopologicalSpace (L ⊗[K] InfiniteAdeleRing K) :=
  moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
-- TODO should be ≃A[L]
/-- The canonical `L`-algebra isomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
def NumberField.InfiniteAdeleRing.baseChangeEquiv :
    (L ⊗[K] (InfiniteAdeleRing K)) ≃A[L] InfiniteAdeleRing L :=
  sorry
