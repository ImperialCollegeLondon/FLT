import FLT.Patching.System

open IsLocalRing Module.UniformlyBoundedRank
attribute [local instance] Module.quotientAnnihilator

-- Let `Λ` be a noetherian local ring, compact with respect to the `𝔪_Λ`-adic topology.
variable (Λ : Type*) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
variable [TopologicalSpace Λ] [IsTopologicalRing Λ] [CompactSpace Λ] [IsAdicTopology Λ]

-- Let `R` be a family of noetherian local `Λ`-algebras, compact with respect to
-- the `𝔪_R`-adic topology.
variable {ι : Type*} (R : ι → Type*)
variable [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, IsNoetherianRing (R i)]
  [∀ i, Algebra Λ (R i)]
variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
variable [∀ i, CompactSpace (R i)] [∀ i, IsAdicTopology (R i)]

-- Let `M i` be a family of nontrivial `R i` modules.
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Nontrivial (M i)] [∀ i, Module Λ (M i)]
variable [∀ i, Module (R i) (M i)] [∀ i, IsScalarTower Λ (R i) (M i)]

-- Let `F` be an ultrafilter on the index set.
variable (F : Ultrafilter ι)

-- For each `k`, the cardinality of `Rᵢ⧸(𝔪_Rᵢ)ᵏ` is uniformly bounded
variable [Algebra.UniformlyBoundedRank R]

variable [∀ i, Module.Free (Λ ⧸ Module.annihilator Λ (M i)) (M i)] -- `Mᵢ` is free
                                                                   -- over `Λ ⧸ Ann Mᵢ`.
variable [Module.UniformlyBoundedRank Λ M] -- `rank_{Λ / Ann Mᵢ} Mᵢ` is finite and uniformly bounded
variable [IsPatchingSystem Λ M F] -- For any open ideal `α ≤ Λ`, `Ann Mᵢ ≤ α` for `F`-many `i`.

-- Let `R₀` be a noetherian local ring, compact with respect to the `𝔪_R₀`-adic topology,
-- and `M₀` an `R₀`-module.
variable {R₀ : Type*} [CommRing R₀] [Algebra Λ R₀] [IsLocalRing R₀] [IsNoetherianRing R₀]
variable [TopologicalSpace R₀] [IsTopologicalRing R₀] [CompactSpace R₀] [IsAdicTopology R₀]
variable {M₀ : Type*} [AddCommGroup M₀] [Module R₀ M₀] [Module Λ M₀] [IsScalarTower Λ R₀ M₀]

-- Suppose there is an ideal `𝔫` of `Λ`,
-- and `Λ`-homomorphisms `Rᵢ⧸𝔫 ≃ R₀` and `Mᵢ⧸𝔫 ≃ M₀` compatible with the module structures.
variable (𝔫 : Ideal Λ)
variable (sR : ∀ i, (R i ⧸ 𝔫.map (algebraMap Λ (R i))) ≃ₐ[Λ] R₀)
variable (sM : ∀ i, (M i ⧸ (𝔫 • ⊤ : Submodule Λ (M i))) ≃ₗ[Λ] M₀)
variable (HCompat : ∀ i m (r : R i),
  sM i (Submodule.Quotient.mk (r • m)) =
  sR i (Ideal.Quotient.mk _ r) • sM i (Submodule.Quotient.mk m))

-- Let `Rₒₒ` be a compact topological domain that is a noetherian local `Λ`-algebra,
-- and is topologically finite generated over `ℤ`.
variable {Rₒₒ : Type*} [CommRing Rₒₒ] [IsNoetherianRing Rₒₒ] [IsLocalRing Rₒₒ] [IsDomain Rₒₒ]
  [Algebra Λ Rₒₒ]
variable [TopologicalSpace Rₒₒ] [CompactSpace Rₒₒ] [IsTopologicalRing Rₒₒ]
  [Algebra.TopologicallyFG ℤ Rₒₒ]
variable [IsLocalHom (algebraMap Λ Rₒₒ)]
variable (fRₒₒ : ∀ i, Rₒₒ →ₐ[Λ] R i)
variable (hfRₒₒ : ∀ i, Function.Surjective (fRₒₒ i)) (hfRₒₒ' : ∀ i, Continuous (fRₒₒ i))

-- Suppose `Rₒₒ` has finite krull dimension, equal to the depth of `Λ`.
variable (H₀ : ringKrullDim Rₒₒ < ⊤) (H : .some (Module.depth Λ Λ) = ringKrullDim Rₒₒ)

-- Let `T₀` be a ring that acts on `M₀`, `R₀ →+* T₀` be a ring homomorphism compatible with
-- the module structure.
variable {T₀ : Type*} [Ring T₀] [Module T₀ M₀]
variable (RtoT : R₀ →+* T₀) (hRtoT : ∀ r (m : M₀), RtoT r • m = r • m)

-- Then `R₀ →+* T₀` has nilpotent kernel.
include F HCompat hfRₒₒ hfRₒₒ' H₀ H hRtoT in
omit [IsNoetherianRing Rₒₒ] in
theorem ker_RtoT_le_nilradical : RingHom.ker RtoT ≤ nilradical R₀ := by
  have : Module.Finite Λ M₀ := by
    cases isEmpty_or_nonempty ι
    · cases F.neBot.1 (Subsingleton.elim _ _)
    have i := Nonempty.some (inferInstanceAs (Nonempty ι))
    exact Module.Finite.equiv (sM i)
  have : Module.Finite R₀ M₀ := .of_restrictScalars_finite Λ _ _
  rw [nilradical, Ideal.radical_eq_sInf, le_sInf_iff]
  rintro p ⟨-, hp⟩
  have := (support_eq_top Λ R M F 𝔫 sR sM fRₒₒ hfRₒₒ hfRₒₒ' HCompat H₀ H).ge (Set.mem_univ ⟨p, hp⟩)
  simp only [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    at this
  refine le_trans ?_ this
  intro x hx
  refine Module.mem_annihilator.mpr fun m ↦ ?_
  rw [← hRtoT, show RtoT x = 0 from hx, zero_smul]
