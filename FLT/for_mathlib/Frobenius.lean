/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.IntegralRestrict
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.FieldTheory.Cardinality


/-!

# Frobenius element for finite extensions L / K

In this file, I :

· formalize the "direct proof" of the existence of the
  Frobenius element for a finite extension of number fields L / K,
  as given by J. S. Milne, in footnote '2' on p. 141 of *Algebraic Number Theory*.

## Main results

- `gal_action_Ideal'` : the action of the Galois group `L ≃ₐ[K] L` on the prime ideals of `B`,
    the ring of integers of `L`.
- `decomposition_subgroup_Ideal'` : the definition of the decomposition subgroup of the
    prime ideal `Q ⊂ B` over `K`.
- `exists_generator` : the proof of the second sentence of Milne's proof :
    "By the Chinese remainder theorem,
    there exists an element `α` of `𝓞 L` such that `α` generates the group `(𝓞 L ⧸ P)ˣ` and
    lies in `τ • P` for all `τ ∉ G(P)`",
    where `G(P)` denotes the decomposition subgroup of `P` over `K`.
    Note that in our file, we rename the non-zero prime ideal `P` as `Q`,
    and we use `P` to denote the non-zero prime ideal of `𝓞 K` over which `Q` lies.
- `coeff_lives_in_A` : for  `F : B[X]` defined to be the product over linear factors whose
                       roots are the Galois conjugates of `α`,  (i.e., `∏ τ : L ≃ₐ[K] L,
                       (X - C (galRestrict A K L B τ α))`),
                       `F` has its coefficients in `A`, where `A` is the ring of integers of
                       the base field `K`.
- `exists_frobenius` : the existence theorem for Frobenius elements of
                       finite Galois extension of number fields.

## Notation

Note that, to define the `MulAction` of `L ≃ₐ[K] L` on the prime ideals of `𝓞 L : = B`,
we used the restriction map `galRestrict`, defined in the file Mathlib.RingTheory.IntegralRestrict.
The definition of `galRestrict` is in terms of an 'AKLB setup'; i.e., where
"`A` is an integrally closed domain; `K` is the fraction ring of `A`; `L` is
a finite (separable) extension of `K`; `B` is the integral closure of
`A` in `L` (Yang & Lutz, 2023, lines 14-15).

In this file, I use the following notation corresponding to an 'AKLB setup':

- `A` : the ring of integers of the number field `K`.
- `K` : a number field of finite dimension over `ℚ`.
- `L` : a number field which is a finite extension of `K`.
- `B` : the ring of integers of the number field `L`.
- `P` : a non-zero prime ideal of `A`.
- `Q` : a non-zero prime ideal of `B` which lies over `P`.
- `Ideal' A K L B`: a redefinition of `Ideal B`, which keeps in mind the existence of
          the ring `A`; this is because the `MulAction` of `L ≃ₐ[K] L` on `Ideal B`
          is defined using `galRestrict`, which requires reference to the scalars `A`
          over which the algebraic equivalence `B ≃ₐ[A] B` is defined.
- `f` : the function assigning a representative non-zero prime ideal of `B` to
          a coset in the quotient `((L ≃ₐ[K] L) ⧸ decomposition_subgroup_Ideal Q)`,
          i.e., an element in the orbit of `Q` under the action of `(L ≃ₐ[K] L)`.
- `p` : a natural prime which is the characteristic of the residue field `(A ⧸ P)`.
- `q` : the cardinality of the residue field `(A ⧸ P)`. We show that `q = p ^ n` for
        some `n : ℕ`.
- `ρ` : `α` in Milne's notation. This `ρ` is an element of `B` which generates the group
          `(B ⧸ Q)ˣ` and is `0` mod `τ • Q` for any `τ` not in the decomposition subgroup
          of `Q` over `K`.
- `α` : local notation for an element `generator : B` which has the properties of `ρ`.
- `F` : local notation for `F' : B[X]`, a polynomial whose roots are exactly the
        Galois conjugates of `α`.
- `m` : local notation for `m' : A[x]`, a polynomial constructed such that its lift to
        `B` under `algebraMap A B` is equal to `F`.
- `Frob` : local notation for `Frob' : L ≃ₐ[K] L`, an element of the Galois group that
           sends `α` to its `q`-th power `mod Q`.
- `γ` : arbitrary element of `B`. We consider the cases `γ ∈ Q`, `γ ∉ Q`, separately.
- `i`:  local notation for `i' : ℕ`, such that `γ ≡ α ^ i mod Q`. `i` depends on `γ`.

## Note : I have changed the previous notation `β → α`, `ν → β`, to conform to Milne's notation.

## Implementation notes

This file was written in Prof. Buzzard's 'FLT' repository.

## References

See [Milne (2020)] footnote '2' on p. 141 (p. 143 in PDF)
  for the proof on which this file is based.

See [Yang & Lutz (2023)], for the definitions of 'AKLB setup' and `galRestrict`.

See [Nakagawa, Baanen, & Filippo (2020)], for the definition of
  `IsDedekindDomain.exists_forall_sub_mem_ideal`,
  the key to proving our theorem `exists_generator`.

See [Karatarakis (2022)], for the definition of 'decomposition subgroup' in terms of
  valuations.

## Acknowledgements

The theorems in this file began life as Jou Glasheen's
2023 Formalising Mathematics student project. Kevin thanks
Jou for taking his class and for writing such a great project.
Jou would particularly like to thank two of Kevin's PhD students, Amelia and Jujian,
for "helping me to understand the math proof and to formalize it."

-/

open Classical

section FiniteFrobeniusDef

variable (A K L B : Type*) [CommRing A] [CommRing B]
  [Algebra A B] [Field K] [Field L]
  [IsDomain A] [IsDomain B]
  [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L] [FiniteDimensional K L] [IsFractionRing B L]
  [IsDedekindDomain A] [IsDedekindDomain B]

/-
**TODO**

The below definition of `Ideal'` needs refactoring somehow, but I am not entirely clear
how yet; perhaps when I understand this work better I'll know how to proceed. Right now
it's the ideals of B but under the assumption that we're in some kind of AKLB set-up.

-/

/-- re-definition of `Ideal B` in terms of 'AKLB setup'. -/
@[nolint unusedArguments] abbrev Ideal' (A K L B : Type*)
  [Semiring B] [SMul A B]
  [SMul A K] [SMul B L]
  [SMul K L] [SMul A L] [IsScalarTower A B L]
  [IsScalarTower A K L]
   := Ideal B

/-
**TODO**

I feel like this definition should be broken into three pieces:

1) Action of `B ≃ₐ[A] B` on `Ideal B`
2) Isomorphism `B ≃ₐ[A] B` = `L ≃ₐ[A] L` if `IsScalarTower A B L`
3) Isomorphism `L ≃ₐ[A] L` = `L ≃ₐ[K] L` if `IsScalarTower A K L`.


-/
/-- Action of the Galois group `L ≃ₐ[K] L` on the prime ideals `(Ideal' A K L B)`;
where `(Ideal' A K L B)` denotes `Ideal B` re-defined with respect to the
'AKLB setup'. -/
noncomputable instance gal_action_Ideal': MulAction (L ≃ₐ[K] L) (Ideal' A K L B) where
  smul σ I := Ideal.comap (AlgEquiv.symm (galRestrict A K L B σ)) I
  one_smul _ := by
    -- `show` unfolds goal into something definitionally equal
    show Ideal.comap _ _ = _
    simp only [map_one]
    exact Ideal.comap_id _
  mul_smul _ _ := by
     intro h
     show Ideal.comap _ _ = _
     simp only [map_mul]
     rfl

-- The following lemma will be used in `CRTRepresentative` (which is why we
-- `@[simp]` it), where it is combined with the assumption (implicit in Milne),
-- that `Q` is a *nonzero* prime ideal of `B`.
-- it is placed here by convention, as a property of `gal_action_Ideal`.
-- Jujian helped me to write this lemma.
@[simp] lemma gal_action_Ideal'.smul_bot (σ : (L ≃ₐ[K] L)) : σ • (⊥ : Ideal' A K L B) = ⊥ := by
  apply Ideal.comap_bot_of_injective
  exact AlgEquiv.injective (AlgEquiv.symm ((galRestrict A K L B) σ))

-- I define the decomposition group of `(Ideal' A K L B)` over `K`
-- to be the stabilizer of the MulAction `gal_action_Ideal'`.

variable {A K L B} in
/-- The decomposition group of `Q : Ideal' A K L B` over `K`.
This is a subgroup of `L ≃ₐ[K] L`. -/
def decomposition_subgroup_Ideal' (Q : Ideal' A K L B) :
  Subgroup (L ≃ₐ[K] L) := MulAction.stabilizer (L ≃ₐ[K] L) Q

-- The following variables introduce instances of the residue fields `(A ⧸ P)` and
-- `(B ⧸ Q)` as finite fields.
variable (P : Ideal A) [Ideal.IsMaximal P] [Fintype (A ⧸ P)] (P_ne_bot : P ≠ ⊥)
  (Q : Ideal' A K L B) [Ideal.IsMaximal Q] [Fintype (B ⧸ Q)] (Q_ne_bot : Q ≠ (⊥ : Ideal B))
  -- This next line was suggested by Amelia Livingston; mathematically it is
  -- equivalent to `P ⊆ A ∩ Q` but it's written purely within the typeclass system.
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]

/-- `Fintype.card (A ⧸ P)` -/
local notation "q" => Fintype.card (A ⧸ P)
-- The main existence proof for the Frobenius element will show that mod `Q` it acts as `x ↦ x^q`.

namespace CRTRepresentative.auxiliary

variable {A K L B} in
/-- Given an ideal `Q`, we have a map `g ↦ g • Q` from `Gal(L/K)` to `Ideal' B`,
which is constant on right cosets of the decomposition group of `Q` over `K`.
Hence it descends to a map from the space space of cosets to `Ideal' B`;
this descent will be injective and will have image the orbit of `Q`. -/
noncomputable def f :
    ((L ≃ₐ[K] L) ⧸ ( decomposition_subgroup_Ideal' Q)) →
    (Ideal' A K L B) :=
  fun x => Quotient.liftOn' x (fun g => g • Q) <| by
    intros σ τ h
    rw [QuotientGroup.leftRel_apply] at h
    -- h : σ⁻¹ * τ ∈ decomposition_subgroup_Ideal' Q
    apply MulAction.mem_stabilizer_iff.1 at h
    -- h : (σ⁻¹ * τ) • Q = Q
    dsimp only
    -- ⊢ σ • Q = τ • Q
    rwa [← eq_inv_smul_iff, eq_comm, smul_smul] -- manipulate
    -- the goal until it becomes `h`, then `rwa` finishes it.

-- The following instance supplies one hypothesis of the CRT.
instance MapPrimestoPrimes (σ : L ≃ₐ[K] L) (Q : Ideal' A K L B) [Ideal.IsPrime Q] :
    Ideal.IsPrime (σ • Q) := Ideal.comap_isPrime (AlgEquiv.symm (galRestrict A K L B σ)) (Q)

end CRTRepresentative.auxiliary

-- The following lemma supplies another hypothesis of the CRT.
lemma coprime_ideals_non_equal_prime (I J : Ideal' A K L B) [Imax : Ideal.IsMaximal I]
    [Jmax : Ideal.IsMaximal J] (h : I ≠ J) : IsCoprime I J := by
  rwa [Ideal.isCoprime_iff_sup_eq, Ideal.IsMaximal.coprime_of_ne Imax Jmax]

section CRTRepresentative
-- We `open Classical`, in order to allow us to use the tactic `if then else`
open CRTRepresentative.auxiliary

-- Jujian helped me to write the following lemma and theorem.
/-- There exists an element of `B` which is equal to the generator `g` of `(B ⧸ Q)ˣ` mod
the coset of `Q` in the orbit of `Q` under `(L ≃ₐ[K] L)`, and
equal to `0` mod any other coset.  -/
lemma crt_representative (b : B) : ∃ (y : B),
    ∀ (i : (L ≃ₐ[K] L) ⧸ decomposition_subgroup_Ideal' Q),
    if i = Quotient.mk'' 1 then y - b ∈ f Q i else y ∈ f Q i := by
  -- We know that we want `IsDedekindDomain.exists_forall_sub_mem_ideal` to
  -- give us the components of the goal,
  -- so we assume `IsDedekindDomain.exists_forall_sub_mem_ideal`,
  -- and dissect it.
  have := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ) (f Q) (fun _ ↦ 1)
    (fun i _ ↦ by
      induction' i using Quotient.inductionOn'  with i
      -- ⊢ Prime (f Q (Quotient.mk'' i))
      change Prime (i • Q)
      apply Ideal.prime_of_isPrime (h := MapPrimestoPrimes A K L B i Q)
      contrapose! Q_ne_bot
      -- goal: (Q_ne_bot : i • Q = ⊥) → Q = ⊥
      apply_fun (i⁻¹ • .) at Q_ne_bot -- that's the hint it needs
      simpa using Q_ne_bot
    )
    (fun i _ j _ hij ↦ by
      induction' i using Quotient.inductionOn'  with i
      induction' j using Quotient.inductionOn'  with j
      change i • Q ≠ j • Q -- goal is this *by definition*
      contrapose! hij
      simp only [Quotient.eq'']
      rw [QuotientGroup.leftRel_eq]
      simp only
      symm at hij
      rw [←inv_smul_eq_iff, smul_smul] at hij
      exact hij
    )
    (fun i ↦ if i = ⟨Quotient.mk'' 1, Finset.mem_univ _⟩ then b else 0)
  choose y hy using this
  use y
  peel hy with hy
  split_ifs <;> simp_all

variable {A K L B Q} in
/--"By the Chinese remainder theorem, there exists an element `ρ` of `B` such that
`ρ` generates the group `(B ⧸ Q)ˣ` and lies in `τ • Q` for all `τ` not in the
decomposition subgroup of `Q` over `K`". -/
theorem exists_generator : ∃ (ρ : B) (h : IsUnit (Ideal.Quotient.mk Q ρ)) ,
    (∀ (x : (B ⧸ Q)ˣ), x ∈ Subgroup.zpowers h.unit) ∧
    (∀ τ : L ≃ₐ[K] L, (τ ∉ decomposition_subgroup_Ideal' Q) →
    ρ ∈ (τ • Q)) := by
  have i : IsCyclic (B ⧸ Q)ˣ := inferInstance
  apply IsCyclic.exists_monoid_generator at i
  rcases i with ⟨⟨g, g', hgg', hg'g⟩, hg⟩
  induction' g using Quotient.inductionOn' with g
  obtain ⟨ρ , hρ⟩ := crt_representative A K L B Q Q_ne_bot g
  use ρ
  have eq1 : (Quotient.mk'' ρ : B ⧸ Q) = Quotient.mk'' g := by
    specialize hρ (Quotient.mk'' 1)
    rw [if_pos rfl] at hρ
    delta f at hρ
    rw [Quotient.liftOn'_mk'', one_smul] at hρ
    simp only [Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk]
    rwa [Ideal.Quotient.eq]
  refine ⟨⟨⟨Quotient.mk'' g, g', hgg', hg'g⟩, eq1.symm⟩, ?_, ?_⟩
  · intro x
    specialize hg x
    set u := _; change x ∈ Subgroup.zpowers u
    suffices equ : u = ⟨Quotient.mk'' g, g', hgg', hg'g⟩ by
      rwa [equ, ← mem_powers_iff_mem_zpowers];
    ext
    simpa only [IsUnit.unit_spec, Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk]
  · intro τ hτ
    specialize hρ (Quotient.mk'' τ)
    have neq1 :
        (Quotient.mk'' τ : (L ≃ₐ[K] L) ⧸ decomposition_subgroup_Ideal' Q) ≠
        Quotient.mk'' 1 := by
      contrapose! hτ
      simpa only [Quotient.eq'', QuotientGroup.leftRel_apply, mul_one, inv_mem_iff] using hτ
    rw [if_neg neq1] at hρ
    delta f at hρ
    rwa [Quotient.liftOn'_mk''] at hρ

end CRTRepresentative

section GalActionIdeal'Supplementary

variable {A K L B Q}

-- this lemma written by Amelia
lemma smul_ideal_eq_map (g : L ≃ₐ[K] L) (I : Ideal' A K L B) :
    g • I = Ideal.map (galRestrict A K L B g) I :=
  Ideal.comap_symm I (galRestrict A K L B g).toRingEquiv

lemma mem_smul_ideal_iff (g : L ≃ₐ[K] L) (I : Ideal' A K L B) (x : B) :
  x ∈ g • I ↔ (galRestrict A K L B g).symm x ∈ I := Iff.rfl

lemma mem_decomposition_iff (g : L ≃ₐ[K] L) :
    g ∈ decomposition_subgroup_Ideal' Q ↔ ∀ x, x ∈ Q ↔
    (galRestrict A K L B g) x ∈ Q := by
  change g • Q = Q ↔ _
  rw [SetLike.ext_iff]
  simp only [mem_smul_ideal_iff]
  constructor
  · intros h x
    constructor
    · intro h1
      specialize h ((galRestrict A K L B) g x)
      simp only [AlgEquiv.symm_apply_apply] at h
      apply h.1 at h1
      exact h1
    · intro h2
      specialize h ((galRestrict A K L B) g x)
      simp only [AlgEquiv.symm_apply_apply] at h
      apply h.2 at h2
      exact h2
  · intros h x
    constructor
    · intro h1
      specialize h (((galRestrict A K L B) g).symm x)
      simp only [AlgEquiv.apply_symm_apply] at h
      apply h.1 at h1
      exact h1
    · intro h2
      specialize h (((galRestrict A K L B) g).symm x)
      simp only [AlgEquiv.apply_symm_apply] at h
      apply h.2 at h2
      exact h2

end GalActionIdeal'Supplementary

open Polynomial BigOperators

/-! ## Freshman's Dream
We show `"q" => Fintype.card (A ⧸ P)` is `p ^ n` for some `(n : ℕ)`, where
`p := Char P (A ⧸ P)`.
Thence, by the ``Freshman's Dream``, for `a : A[X]`,
we have `a(X ^ q) ≡ a(X) ^ q mod P`.  -/
section FreshmansDream

variable {A K L B Q}

-- local notation "q" => Fintype.card (A ⧸ P) -- show this is a power of a prime
noncomputable instance : Field (A ⧸ P) := Ideal.Quotient.field P

lemma is_primepow_char_A_quot_P : IsPrimePow q := Fintype.isPrimePow_card_of_field

lemma ex_primepow_char_A_quot_P : ∃ p n : ℕ , Prime p ∧ 0 < n ∧ p ^ n = q := by
  exact is_primepow_char_A_quot_P _

local notation "p" => Classical.choose (CharP.exists (A ⧸ P))
local notation "p'" => Classical.choose (ex_primepow_char_A_quot_P P)
local notation "n" => Classical.choose (Classical.choose_spec (ex_primepow_char_A_quot_P P))

instance p_is_char : CharP (A ⧸ P) p := Classical.choose_spec (CharP.exists (A ⧸ P))

lemma p_is_prime : (Nat.Prime p) := char_prime_of_ne_zero (A ⧸ P) <|
  CharP.char_ne_zero_of_finite (A ⧸ P) _

lemma p'_is_prime : Nat.Prime p' :=
  Nat.prime_iff.mpr <| (ex_primepow_char_A_quot_P P).choose_spec.choose_spec.1

lemma q_is_p'_pow_n : p' ^ n = q :=
  Classical.choose_spec (Classical.choose_spec (ex_primepow_char_A_quot_P P)) |>.2.2

lemma p_is_p' : p = p' := by
  -- `q = 0` in `A⧸ P` and `p | q` since `CharP p` then since `q = p' ^ n` then `p' = p`
  have eq0 : (q : A⧸ P) = 0 := sorry--CharP.cast_card_eq_zero (A ⧸ P) -- mathlib bump broke this
  have h1 : p ∣ q := charP_iff (A ⧸ P) p |>.1 (p_is_char P) q |>.1 eq0
  have eq1 : p' ^ n = q := q_is_p'_pow_n P
  rw [← eq1] at h1
  exact Nat.dvd_prime (p'_is_prime P) |>.1
    (Nat.Prime.dvd_of_dvd_pow (p_is_prime P) h1) |>.resolve_left <| Nat.Prime.ne_one <| p_is_prime P

lemma q_is_p_pow_n : p ^ n = q := by
  rw [p_is_p', q_is_p'_pow_n]

/-- By the ``Freshman's Dream``, for `a : A[X]`,
we have `a(X ^ q) ≡ a(X) ^ q mod P,` where
`q` is the cardinality of the residue field `(A ⧸ P)`. -/
theorem pow_eq_expand (a : (A ⧸ P)[X]) :
    (a ^ q) = (expand _ q a)  := by
  have pprime : Nat.Prime p := p_is_prime P
  have factprime : Fact (Nat.Prime p) := { out := pprime }
  rw [← q_is_p_pow_n, ← map_expand_pow_char, map_expand, FiniteField.frobenius_pow]
  · simp [exists_and_left, RingHom.one_def, map_id]
  · exact (q_is_p_pow_n P).symm

end FreshmansDream

section generator

variable {A K L B Q}

/-- `α` is an element of `B` such that `IsUnit (Ideal.Quotient.mk Q α))`,
`α` generates the group `(B ⧸ Q)ˣ)`; and
`∀  τ : L ≃ₐ[K] L, (τ ∉ decomposition_subgroup_Ideal'  A K L B Q),
α ∈ (τ • Q)))`.  -/
noncomputable def generator : B :=
  Classical.choose (exists_generator Q_ne_bot)

-- Jujian suggested and helped with the following lemmas:
lemma generator_isUnit : IsUnit (Ideal.Quotient.mk Q (generator Q_ne_bot)) :=
  (Classical.choose_spec (exists_generator Q_ne_bot)).choose

lemma generator_mem_zpowers :
    ∀ (x : (B ⧸ Q)ˣ), x ∈ Subgroup.zpowers (generator_isUnit Q_ne_bot).unit :=
  (Classical.choose_spec (exists_generator Q_ne_bot)).choose_spec.1

lemma generator_mem_submonoid_powers (x : (B ⧸ Q)ˣ) :
    x ∈ Submonoid.powers (generator_isUnit Q_ne_bot).unit := by
  classical
  have h := IsCyclic.image_range_orderOf (generator_mem_zpowers Q_ne_bot)
  have hx : x ∈ Finset.univ := by simp only [Finset.mem_univ]
  rw [← h] at hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  rcases hx with ⟨n, _, hn2⟩
  use n

lemma generator_well_defined : (∀ τ : L ≃ₐ[K] L, (τ ∉ decomposition_subgroup_Ideal' Q) →
   (generator Q_ne_bot) ∈ (τ • Q)) :=
  (Classical.choose_spec (exists_generator Q_ne_bot)).choose_spec.2

end generator

/-- `generator A K L B Q Q_ne_bot` -/
local notation "α" => generator Q_ne_bot

open BigOperators

-- Jujian helped with the following def:
/-- `F : B[X]` defined to be a product of linear factors `(X - τ • α)`; where
`τ` runs over `L ≃ₐ[K] L`, and `α : B` is an element which generates `(B ⧸ Q)ˣ`
and lies in `τ • Q` for all `τ ∉ (decomposition_subgroup_Ideal'  A K L B Q)`.-/
noncomputable def F' : B[X] := ∏ τ : L ≃ₐ[K] L,
    (X - C (galRestrict A K L B τ α))

/-- `F' A K L B Q Q_ne_bot` -/
local notation "F" => F' A K L B Q Q_ne_bot

variable [IsGalois K L] [IsIntegralClosure A A K]

namespace coeff_lives_in_A.auxiliary
/-- The action of automorphisms `σ : L ≃ₐ[K] L` on linear factors of `F` acts as
scalar multiplication on the constants `C (galRestrict A K L B τ (α))`.  -/
theorem gal_smul_F_eq  (σ : L ≃ₐ[K] L) :
    galRestrict A K L B σ •
    (∏ τ : L ≃ₐ[K] L,
      (X - C (galRestrict A K L B τ α))) =
    ∏ τ : L ≃ₐ[K] L,
    (X - C (galRestrict A K L B σ
      (galRestrict A K L B τ α))):= by
  simp [Finset.smul_prod, smul_sub, smul_X, smul_C, AlgEquiv.smul_def]

/-- use `Finset.prod_bij` to show
`(galRestrict A K L B σ • (∏ τ : L ≃ₐ[K] L, (X - C (galRestrict A K L B τ α))) =
(∏ τ : L ≃ₐ[K] L, (X - C (galRestrict A K L B τ α)))` -/
lemma F_invariant_under_finite_aut (σ :  L ≃ₐ[K] L)  :
    ∏ τ : L ≃ₐ[K] L, (X - C (galRestrict A K L B σ
    (galRestrict A K L B τ α))) = F := by
  set i : (τ : L ≃ₐ[K] L) → τ ∈ Finset.univ → L ≃ₐ[K] L := fun τ _ => σ * τ
  -- needed to use `set i` instead of `have i`, in order to be able to use `i` later on, in proof
  have hi : ∀ (τ : L ≃ₐ[K] L) (hτ : τ ∈ Finset.univ), i τ hτ ∈ Finset.univ := by
    simp [Finset.mem_univ, forall_true_left, forall_const]
  have i_inj : ∀ (τ₁ : L ≃ₐ[K] L) (hτ₁ : τ₁ ∈ Finset.univ) (τ₂ : L ≃ₐ[K] L)
      (hτ₂ : τ₂ ∈ Finset.univ), i τ₁ hτ₁ = i τ₂ hτ₂ → τ₁ = τ₂ := by
    intros τ₁ _ τ₂ _ h
    simpa [i, mul_right_inj] using h
  have i_surj : ∀ σ ∈ Finset.univ, ∃ (τ : L ≃ₐ[K] L) (hτ : τ ∈ Finset.univ), i τ hτ = σ := by
    intro τ'
    simp only [Finset.mem_univ, exists_true_left, forall_true_left, i]
    use (σ⁻¹ * τ')
    group
  have h : ∀ (τ : L ≃ₐ[K] L) (hτ : τ ∈ Finset.univ),
      (X - C (galRestrict A K L B σ (galRestrict A K L B τ α))) =
      (X - C (galRestrict A K L B (i τ hτ) α)) := by
    intros τ hτ
    simp only [i, map_mul, sub_right_inj, C_inj]
    rw [AlgEquiv.aut_mul]
    rfl
  exact Finset.prod_bij i hi i_inj i_surj h

/-- ` L ≃ₐ[K] L` fixes `F`. -/
theorem gal_smul_F_eq_self (σ : L ≃ₐ[K] L) :
     galRestrict A K L B σ • (∏ τ : L ≃ₐ[K] L,
     (X - C (galRestrict A K L B τ α))) =
     (∏ τ : L ≃ₐ[K] L, (X - C (galRestrict A K L B τ α))) := by
  rw [gal_smul_F_eq, F_invariant_under_finite_aut]
  rfl

theorem gal_smul_coeff_eq (n : ℕ) (h : ∀ σ : L ≃ₐ[K] L, galRestrict A K L B σ • F = F)
    (σ : L ≃ₐ[K] L) : galRestrict A K L B σ • (coeff F n) = coeff F n := by
  nth_rewrite 2 [← h σ]
  simp [coeff_smul, AlgEquiv.smul_def]

variable {A K L B Q}

theorem coeff_lives_in_fixed_field (n : ℕ) :
    (algebraMap B L (coeff F n : B) : L) ∈
      IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
  change ∀ _, _
  rintro ⟨σ, -⟩
  change σ _ = _
  rw [← algebraMap_galRestrict_apply A]
  have h := gal_smul_F_eq_self A K L B Q Q_ne_bot σ
  apply_fun (coeff · n) at h
  rw [coeff_smul] at h
  change (galRestrict A K L B) σ (coeff F n) = coeff F n at h
  congr 1

lemma coeff_lives_in_K (n : ℕ) : ∃ k : K, algebraMap B L (coeff F n) = (algebraMap K L k) := by
  have eq0 := ((@IsGalois.tfae K _ L _ _ _).out 0 1).mp (by infer_instance)
  have h := coeff_lives_in_fixed_field Q_ne_bot n
  rw [eq0] at h
  change _ ∈ (⊥ : Subalgebra _ _) at h
  rw [Algebra.mem_bot] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨_, hk.symm⟩

end coeff_lives_in_A.auxiliary

variable {A K L B Q}

open coeff_lives_in_A.auxiliary in
theorem coeff_lives_in_A (n : ℕ) : ∃ a : A, algebraMap B L (coeff F n) = (algebraMap A L a) := by
  obtain ⟨k, hk⟩ := coeff_lives_in_K Q_ne_bot n
  have h1 := IsIntegralClosure.isIntegral_iff (A := A) (R := A) (B := K) (x := k)
  obtain ⟨p, p_monic, hp⟩ := IsIntegralClosure.isIntegral_iff
    (A := B) (R := A) (B := L) (x := (algebraMap B L) (coeff F n)) |>.mpr ⟨coeff F n, rfl⟩
  have eq0 : algebraMap A L = (algebraMap K L).comp (algebraMap A K) := by
    ext
    exact (IsScalarTower.algebraMap_apply A K L _)
  have h2 : IsIntegral A k := by
    refine ⟨p, p_monic, ?_⟩
    rw [hk, eq0, ←  Polynomial.hom_eval₂] at hp
    apply (map_eq_zero_iff _ _).1 hp
    exact NoZeroSMulDivisors.algebraMap_injective K L
  cases' h1.1 h2 with a' ha'
  use a'
  simpa [eq0, RingHom.coe_comp, Function.comp_apply, ha']

/-- `α` is a root of `F`. -/
lemma isRoot_α : eval α F = 0 := by
  have evalid : eval α (X - C ((α))) = 0 := by
    simp only [eval_sub, eval_X, eval_C, sub_self]
  have eqF : (eval α (∏ τ : L ≃ₐ[K] L,
      (X - C (galRestrict A K L B τ α)))) = eval α F := rfl
  have eq0 : (eval α (X - C ((α))) = 0) → (eval α (∏ τ : L ≃ₐ[K] L,
      (X - C (galRestrict A K L B τ α))) = 0) := by
    intro _
    rw [Polynomial.eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    apply Finset.prod_eq_zero_iff.2
    use 1
    constructor
    · simp only [Finset.mem_univ]
    · simp only [map_one]
      change α - α = 0
      rw [sub_self]
  apply eq0 at evalid
  rwa [← eqF]

lemma quotient_isRoot_α : (eval α F) ∈ Q := (isRoot_α Q_ne_bot) ▸ Ideal.zero_mem _

lemma conjugate_isRoot_α (σ : L ≃ₐ[K] L) : (eval (galRestrict A K L B σ α) F) = 0 := by
  have evalσ : eval  (galRestrict A K L B σ α)
      (X - C (galRestrict A K L B σ α)) = 0 := by
    simp [eval_sub, eval_X, eval_C, sub_self]
  have eqF : (eval (galRestrict A K L B σ α) (∏ τ : L ≃ₐ[K] L,
      (X - C (galRestrict A K L B τ α)))) =
      eval (galRestrict A K L B σ α) F := rfl
  have eq0 : (eval  (galRestrict A K L B σ α)
      (X - C (galRestrict A K L B σ α)) = 0) →
      ((eval (galRestrict A K L B σ α) (∏ τ : L ≃ₐ[K] L,
      (X - C (galRestrict A K L B τ α)))) = 0) := by
    intro _
    rw [Polynomial.eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    apply Finset.prod_eq_zero_iff.2
    use σ
    constructor
    · simp only [Finset.mem_univ]
    · simp only [sub_self]
  apply eq0 at evalσ
  rw [← eqF, evalσ]

lemma conjugate_quotient_isRoot_α (σ : L ≃ₐ[K] L) :
    (eval (galRestrict A K L B σ α) F) ∈ Q := (conjugate_isRoot_α Q_ne_bot) _ ▸ Ideal.zero_mem _

lemma F_is_root_iff_is_conjugate {x : B} :
    IsRoot F x ↔ (∃ σ : L ≃ₐ[K] L, x = (galRestrict A K L B σ α)) := by
  constructor
  · intro h
    rw [Polynomial.IsRoot.def] at h
    have eqF : eval x (∏ τ : L ≃ₐ[K] L,
      (X - C ((galRestrict A K L B τ) α))) =
      eval x F := rfl
    rw [← eqF, Polynomial.eval_prod] at h
    suffices _ : ∃ σ : L ≃ₐ[K] L, eval x (X - C ((((galRestrict A K L B) σ)) α)) = 0 by
      rw [Finset.prod_eq_zero_iff] at h
      rcases h with ⟨a, _, ha2⟩
      rw [← Polynomial.IsRoot.def] at ha2
      apply Polynomial.root_X_sub_C.1 at ha2
      use a
      exact ha2.symm
    rw [Finset.prod_eq_zero_iff] at h
    rcases h with ⟨a', _, haa2⟩
    use a'
  · intros h
    rcases h with ⟨σ, hσ⟩
    rw [Polynomial.IsRoot.def, hσ]
    exact conjugate_isRoot_α Q_ne_bot _

lemma F_eval_zero_is_conjugate {x : B} (h : eval x F = 0) : ∃ σ : L ≃ₐ[K] L,
    x = ((galRestrict A K L B σ) α) := by
  rwa [← Polynomial.IsRoot.def, F_is_root_iff_is_conjugate] at h

-- make a polynomial with coefficients in `A`
lemma ex_poly_in_A : ∃ m : A[X], Polynomial.map (algebraMap A B) m = F := by
  have h (n : ℕ) : ∃ a : A, algebraMap B L (coeff F n) = (algebraMap A L a) :=
    coeff_lives_in_A Q_ne_bot n
  let m : A[X] := {
    toFinsupp := {
      support := Polynomial.support F
      toFun := fun n => Classical.choose (h n)
      mem_support_toFun := by
        intro n
        simp only [mem_support_iff, ne_eq]
        have := Classical.choose_spec (h n)
        set s := Classical.choose (h n)
        apply Iff.not
        rw [← _root_.map_eq_zero_iff (algebraMap B L), this, map_eq_zero_iff]
        have I : NoZeroSMulDivisors A L := NoZeroSMulDivisors.trans A K L
        · exact NoZeroSMulDivisors.algebraMap_injective _ _
        · exact NoZeroSMulDivisors.algebraMap_injective _ _
        }}
  use m
  ext n
  simp only [coeff_map, coeff_ofFinsupp, Finsupp.coe_mk]
  set s := Classical.choose (h n)
  apply NoZeroSMulDivisors.algebraMap_injective B L
  exact (Classical.choose_spec (h n)) ▸ (IsScalarTower.algebraMap_apply A B L _).symm

/--`m' : A[X]` such that `Polynomial.map (algebraMap A B) m = F`.  -/
noncomputable def m' : A[X] := Classical.choose (ex_poly_in_A Q_ne_bot)

local notation "m" => m' Q_ne_bot

lemma m_mapsto_F : Polynomial.map (algebraMap A B) m = F :=
  Classical.choose_spec (ex_poly_in_A Q_ne_bot)

lemma m_eq_F_in_B_quot_Q :
    Polynomial.map (algebraMap B (B ⧸ Q)) (Polynomial.map (algebraMap A B) m) =
    Polynomial.map (algebraMap B (B ⧸ Q)) F := by
  suffices h : Polynomial.map (algebraMap A B) m = F  by
    exact congrArg (map (algebraMap B (B ⧸ Q))) h
  exact m_mapsto_F _

lemma m_expand_char_q : (Polynomial.map (algebraMap A (A ⧸ P)) m) ^ q =
    (expand _ q (Polynomial.map (algebraMap A (A ⧸ P)) m)) := by
  exact pow_eq_expand _ _

lemma B_m_expand_char_q : (Polynomial.map (algebraMap A (B ⧸ Q)) m) ^ q =
    (expand _ q (Polynomial.map (algebraMap A (B ⧸ Q)) m)) := by
  have st : (algebraMap A (B ⧸ Q)) =
      RingHom.comp (algebraMap (A ⧸ P) (B ⧸ Q)) (algebraMap A (A ⧸ P)) :=
    IsScalarTower.algebraMap_eq A (A ⧸ P)  (B ⧸ Q)
  rw [st, ← Polynomial.map_map, ← Polynomial.map_pow, m_expand_char_q, map_expand]

lemma A_B_scalar_tower_m : Polynomial.map (algebraMap A (B ⧸ Q)) m =
    Polynomial.map (RingHom.comp (algebraMap B (B ⧸ Q)) (algebraMap A B)) m := by
  have st : (algebraMap A (B ⧸ Q)) =
      RingHom.comp (algebraMap B (B ⧸ Q)) (algebraMap A B) :=
    IsScalarTower.algebraMap_eq A B (B ⧸ Q)
  rw [st]

lemma pow_expand_A_B_scalar_tower_m :
    (( Polynomial.map ( RingHom.comp (algebraMap B (B ⧸ Q)) (algebraMap A B))) m) ^ q =
    (expand _ q ( Polynomial.map ( RingHom.comp (algebraMap B (B ⧸ Q)) (algebraMap A B) ) m)) := by
  have h : (Polynomial.map (algebraMap A (B ⧸ Q)) m) ^ q =
    (expand _ q (Polynomial.map (algebraMap A (B ⧸ Q)) m)) := B_m_expand_char_q P Q_ne_bot
  rwa [← A_B_scalar_tower_m]

lemma pow_expand_A_B_scalar_tower_F :
    ( Polynomial.map (algebraMap B (B ⧸ Q)) F) ^ q =
    (expand _ q ( Polynomial.map (algebraMap B (B ⧸ Q)) F)) := by
  have h :  (( Polynomial.map ( RingHom.comp (algebraMap B (B ⧸ Q)) (algebraMap A B))) m) ^ q =
      (expand _ q ( Polynomial.map ( RingHom.comp (algebraMap B (B ⧸ Q)) (algebraMap A B) ) m)) :=
    pow_expand_A_B_scalar_tower_m P Q_ne_bot
  rwa [← m_mapsto_F, Polynomial.map_map]

lemma F_expand_eval_eq_eval_pow :
    (eval₂ (Ideal.Quotient.mk Q) (Ideal.Quotient.mk Q α) F) ^ q =
    (eval₂ (Ideal.Quotient.mk Q) (Ideal.Quotient.mk Q (α ^ q)) F) := by
  simp_rw [← Polynomial.eval_map,  ←  Ideal.Quotient.algebraMap_eq, ← Polynomial.coe_evalRingHom,
    ← map_pow, pow_expand_A_B_scalar_tower_F, Ideal.Quotient.algebraMap_eq, coe_evalRingHom,
    expand_eval, map_pow]

lemma quotient_F_is_product_of_quot :
    (Polynomial.map (Ideal.Quotient.mk Q) F) =
    ∏ τ : L ≃ₐ[K] L, (X - C ((Ideal.Quotient.mk Q) ((galRestrict A K L B τ) α))) := by
  rw [← Polynomial.coe_mapRingHom]
  erw [map_prod]
  simp [map_sub, coe_mapRingHom, map_X, map_C]

lemma quotient_F_is_root_iff_is_conjugate (x : (B ⧸ Q)) :
    IsRoot (Polynomial.map  (Ideal.Quotient.mk Q) F) x ↔
    (∃ σ : L ≃ₐ[K] L, x = ((Ideal.Quotient.mk Q) ((galRestrict A K L B σ) α)))  := by
  rw [quotient_F_is_product_of_quot, Polynomial.isRoot_prod]
  simp only [Finset.mem_univ, eval_sub, eval_X, eval_C, true_and, Polynomial.root_X_sub_C]
  simp [eq_comm]

lemma pow_eval_root_in_Q : ((eval α F) ^ q) ∈ Q := by
  have h : (eval α F) ∈ Q := quotient_isRoot_α Q_ne_bot
  apply Ideal.pow_mem_of_mem
  · exact h
  · exact Fintype.card_pos

lemma expand_eval_root_eq_zero :
    (eval₂ (Ideal.Quotient.mk Q) (Ideal.Quotient.mk Q (α ^ q)) F) = 0 := by
  simp only [← F_expand_eval_eq_eval_pow P Q_ne_bot, eval₂_at_apply, ne_eq, Fintype.card_ne_zero,
    not_false_eq_true, pow_eq_zero_iff]
  have h : eval α F ∈ Q := quotient_isRoot_α Q_ne_bot
  rwa [← Ideal.Quotient.eq_zero_iff_mem] at h

-- now, want `∃ σ, α ^ q ≡ σ α mod Q`
lemma pow_q_is_conjugate : ∃ σ : L ≃ₐ[K] L, (Ideal.Quotient.mk Q (α ^ q)) =
    (Ideal.Quotient.mk Q ((((galRestrict A K L B) σ)) α)) := by
  rw [← quotient_F_is_root_iff_is_conjugate, map_pow, IsRoot.def, Polynomial.eval_map]
  exact expand_eval_root_eq_zero P Q_ne_bot

-- following lemma suggested by Amelia
lemma pow_quotient_IsRoot_α : (eval (α ^ q) F) ∈ Q := by
  rw [←  Ideal.Quotient.eq_zero_iff_mem]
  have h2 : (eval₂ (Ideal.Quotient.mk Q) (Ideal.Quotient.mk Q (α ^ q)) F) = 0 :=
    expand_eval_root_eq_zero P Q_ne_bot
  convert h2
  rw [eval₂_at_apply]

/--`α ^ q ≡ σ • α mod Q` for some `σ : L ≃ₐ[K] L` -/
lemma pow_q_conjugate :
    ∃ σ : L ≃ₐ[K] L, (α ^ q - (galRestrict A K L B σ) α) ∈ Q := by
  convert pow_q_is_conjugate P Q_ne_bot
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]

/--`Frob' : L ≃ₐ[K] L` such that ` (α ^ q - (galRestrict A K L B σ) α) ∈ Q`.   -/
noncomputable def Frob' : L ≃ₐ[K] L := Classical.choose (pow_q_conjugate P Q_ne_bot)

local notation "Frob" => Frob' P Q_ne_bot

/-- if `Frob ∉ decomposition_subgroup_Ideal' A K L B Q`, then `Frob⁻¹ • Q ≠ Q` -/
lemma inv_aut_not_mem_decomp (h : Frob ∉ decomposition_subgroup_Ideal' Q) : (Frob⁻¹ • Q) ≠ Q := by
  by_contra con
  apply inv_smul_eq_iff.1 at con
  exact h (id con.symm)

/-- `α ∈ Frob⁻¹ • Q`. -/
lemma gen_zero_mod_inv_aut (h1 : Frob ∉ decomposition_subgroup_Ideal' Q) :
    α ∈ (Frob⁻¹ • Q) := by
  have inv : Frob⁻¹ ∉ decomposition_subgroup_Ideal' Q := by
    simpa [inv_mem_iff]
  exact generator_well_defined _ _ inv

lemma prop_Frob : (α ^ q - (galRestrict A K L B Frob) α) ∈ Q :=
  Classical.choose_spec (pow_q_conjugate P Q_ne_bot)

-- proof of this lemma written by Amelia:
lemma inv_Frob (h : α ∈ (Frob⁻¹ • Q)) : ((galRestrict A K L B Frob) α) ∈ Q := by
   change (galRestrict A K L B Frob⁻¹).symm α ∈ Q at h
   simp_all only [ne_eq, map_inv]
   convert h

/-- If `α ∈ Frob⁻¹ • Q`, then `α ^ q ≡ Frob • α ≡ 0 mod Q.` -/
lemma is_zero_pow_gen_mod_Q (h : α ∈ (Frob⁻¹ • Q)) :
    (α ^ q) ∈ Q := by
  have h1 : (galRestrict A K L B Frob) α ∈ Q := inv_Frob P Q_ne_bot h
  have h2 : (α ^ q - (galRestrict A K L B Frob) α) ∈ Q :=
    Classical.choose_spec (pow_q_conjugate P Q_ne_bot)
  rw [← Ideal.neg_mem_iff] at h1
  have h3 : ((α ^ q - (galRestrict A K L B Frob) α) -
      (-(galRestrict A K L B Frob) α)) ∈ Q := by
    exact Ideal.sub_mem Q h2 h1
  convert h3
  simp [sub_neg_eq_add, sub_add_cancel]

/-- `Frob ∈ decomposition_subgroup_Ideal'  A K L B Q`. -/
theorem Frob_is_in_decompositionSubgroup :
    Frob ∈ decomposition_subgroup_Ideal' Q := by
  by_contra con
  apply IsUnit.ne_zero <| generator_isUnit Q_ne_bot
  exact Ideal.Quotient.eq_zero_iff_mem.2 <|
    Ideal.IsPrime.mem_of_pow_mem (hI := inferInstance)
    (H := is_zero_pow_gen_mod_Q (h := gen_zero_mod_inv_aut (h1 := con)))

/- ## Now, for `γ : B` we have two cases: `γ ∉ Q` and `γ ∈ Q`. -/

/-- Every element `γ : B`, `γ ∉ Q`, can be written `γ = α ^ i + β`, with `β ∈ Q` -/
lemma γ_not_in_Q_is_pow_gen {γ : B} (h : γ ∉ Q) :  ∃ (i : ℕ), γ - (α ^ i) ∈ Q := by
   let g :=  Units.mk0 (((Ideal.Quotient.mk Q γ))) <| by
    intro h1
    rw [Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h h1
   rcases generator_mem_submonoid_powers Q_ne_bot g with ⟨i, hi⟩
   use i
   rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
   simp [g, Units.ext_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_mk0] at hi
   simp [g, map_pow, hi]

/--`i' : ℕ` such that, for `(γ : B) (h : γ ∉ Q)`, `γ - (α ^ i) ∈ Q`. -/
noncomputable def i' {γ : B} (h : γ ∉ Q) : ℕ :=
  (Classical.choose (γ_not_in_Q_is_pow_gen Q_ne_bot h))

local notation "i" => i' Q_ne_bot

lemma prop_γ_not_in_Q_is_pow_gen {γ : B} (h : γ ∉ Q) : γ - (α ^ (i h)) ∈ Q :=
  (γ_not_in_Q_is_pow_gen Q_ne_bot h).choose_spec

/-- `Frob • γ ≡ Frob • (α ^ i) mod Q` -/
lemma eq_pow_gen_apply {γ : B} (h: γ ∉ Q) : (galRestrict A K L B Frob) γ -
    galRestrict A K L B Frob (α ^ (i h)) ∈ Q := by
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have h1 : γ - (α ^ (i h)) ∈ Q := prop_γ_not_in_Q_is_pow_gen Q_ne_bot h
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.Quotient.eq] at h1
  rw [Ideal.Quotient.eq, ← map_sub]
  have := Frob_is_in_decompositionSubgroup P Q_ne_bot
  rw [mem_decomposition_iff] at this
  exact (this _).1 h1

-- γ ∈ B \ Q is α^i mod Q
/-- `Frob • (α ^ i)  ≡ α ^ (i * q) mod Q` -/
lemma pow_pow_gen_eq_pow_gen_apply {γ : B} {h : γ ∉ Q} : ((α ^ ((i h) * q)) -
    galRestrict A K L B Frob (α ^ (i h))) ∈ Q := by
  have h1 : α ^ q - (galRestrict A K L B Frob) α ∈ Q := prop_Frob P Q_ne_bot
  simp_all only [ne_eq, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem, map_pow]
  rw [pow_mul']
  exact congrFun (congrArg HPow.hPow h1) (i h)

/--  `α ^ (i * q) ≡ γ ^ q mod Q` -/
lemma pow_pow_gen_eq_pow {γ : B} (h : γ ∉ Q) : ((α ^ ((i h) * q)) -
    (γ ^ q)) ∈ Q := by
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have h1 : γ - (α ^ (i h)) ∈ Q := prop_γ_not_in_Q_is_pow_gen Q_ne_bot h
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h1
  rw [mul_comm, pow_mul']
  simp only [map_pow]
  exact congrFun (congrArg HPow.hPow (id h1.symm)) q

/-- Case `γ ∉ Q` : then `Frob γ ≡ γ ^ q mod Q`.  -/
theorem Frob_γ_not_in_Q_is_pow {γ : B} (h : γ ∉ Q) :
    ((γ ^ q) - (galRestrict A K L B Frob) γ) ∈ Q := by
  have  h2 : (galRestrict A K L B Frob) γ -
      (galRestrict A K L B Frob) (α ^ (i h)) ∈ Q := eq_pow_gen_apply P Q_ne_bot h
  have h3 : ((α ^ ((i h) * q)) -
      (galRestrict A K L B Frob) (α ^ (i h))) ∈ Q := pow_pow_gen_eq_pow_gen_apply P Q_ne_bot
  have h4 : ((α ^ ((i h) * q)) - (γ ^ q)) ∈ Q := pow_pow_gen_eq_pow P Q_ne_bot h
  have h5 : (((galRestrict A K L B Frob) γ -
      (galRestrict A K L B Frob) (α ^ (i h))) - ( ((α ^ ((i h) * q)) -
      (galRestrict A K L B Frob) (α ^ (i h))))) ∈ Q := by
    apply Ideal.sub_mem
    · exact h2
    · exact h3
  simp only [map_pow, sub_sub_sub_cancel_right] at h5
  have h6 : (( (((galRestrict A K L B) Frob)) γ - α ^ (i h * q)) +
      (((α ^ ((i h) * q)) - (γ ^ q)))) ∈ Q := Ideal.add_mem _ h5 h4
  simp only [sub_add_sub_cancel] at h6
  rw [← Ideal.neg_mem_iff] at h6
  simp only [neg_sub] at h6
  exact h6

/- ## Now, we consider the case `γ : Q`.-/

/-- Case `γ ∈ Q` : then `Frob γ ≡ γ ^ q mod Q`.  -/
theorem Frob_γ_in_Q_is_pow {γ : B} (h : γ ∈ Q) :
    ((γ ^ q) - (galRestrict A K L B Frob) γ) ∈ Q := by
  apply Ideal.sub_mem
  · apply Ideal.pow_mem_of_mem at h
    specialize h q
    apply h
    exact Fintype.card_pos
  · exact ((mem_decomposition_iff Frob).1
      (Frob_is_in_decompositionSubgroup P Q_ne_bot) γ).1 h

lemma for_all_gamma (γ : B) : ((γ ^ q) - (galRestrict A K L B Frob) γ) ∈ Q := by
  have h1 : if (γ ∉ Q) then ((γ ^ q) - (galRestrict A K L B Frob) γ) ∈ Q
      else ((γ ^ q) - (galRestrict A K L B Frob) γ) ∈ Q := by
    split_ifs with H
    · apply Frob_γ_in_Q_is_pow P Q_ne_bot at H
      simp only at H
      convert H
    · apply Frob_γ_not_in_Q_is_pow P Q_ne_bot at H
      exact H
  aesop

/--Let `L / K` be a finite Galois extension of number fields, and let `Q` be a prime ideal
of `B`, the ring of integers of `L`. Then, there exists an element `σ : L ≃ₐ[K] L`
such that `σ` is in the decomposition subgroup of `Q` over `K`;
and `∀ γ : B`,  `(γ ^ q) - (galRestrict A K L B σ) γ) ∈ Q`,
i.e., `σγ ≡ γ ^ q mod Q`;
where `q` is the number of elements in the residue field `(A ⧸ P)`,
`P = Q ∩ K`, and `A` is the ring of integers of `K`.  -/
theorem exists_frobenius :
    ∃ σ : L ≃ₐ[K] L,
      (σ ∈ decomposition_subgroup_Ideal' Q ) ∧
      (∀ γ : B, ((γ ^ q) - (galRestrict A K L B σ) γ) ∈ Q) :=
  ⟨Frob, Frob_is_in_decompositionSubgroup P Q_ne_bot, fun γ => for_all_gamma P Q_ne_bot γ⟩

end FiniteFrobeniusDef
