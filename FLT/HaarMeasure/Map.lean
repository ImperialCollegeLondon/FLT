import Mathlib
/-

# Scaling Haar measure

If `G` is a locally compact topological group then it has a Haar measure, unique up to a
positive real constant. If `φ : G ≃* G` is a topological isomorphism and we fix a Haar measure
on the source `G`, then its pushforward is a Haar measure on the target `G`, which is
thus equal to `Δ(φ)` times the original Haar measure, where `Δ(φ)` is a positive real number.
It is easily checked that `Δ(φ)` is independent of the choice of Haar measure, and that it
is multiplicative on the group of topological group endomorphisms of `G`.

## Applications

1) The modular character of a locally compact topological group
2) The canonical norm on the units of a locally compact topological ring

## Thoughts

Probably some auxiliary functions need to be defined first. For example I could imagine
a private `delta_aux` function which depends on a choice of Haar measure, and then
a proof that it's independent of the choice.
See discussion at https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/canonical.20norm.20coming.20from.20Haar.20measure/near/480050592
for more hints.
-/

-- this is what I need for FLT
open MeasureTheory in
/-- Multiplicative scaling factor for additive Haar measure on a locally compact
topological ring. `scale r` is the positive real constant such that `μ(rU)=scale r * μ(U)`
where μ is a Haar measure. This is easily checked to be independent of the choice of Haar measure. -/
def TopologicalRing.AddHaarMeasure.scale (R : Type*) [Ring R] [TopologicalSpace R]
    [TopologicalRing R] [LocallyCompactSpace R] :
    Rˣ →* ℝ := by
  sorry
