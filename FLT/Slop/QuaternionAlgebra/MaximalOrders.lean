/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.KnownIn1980s.QuaternionAlgebra.MaximalOrders.Defs

/-!
# Proof of maximal orders in quaternion algebras

Proof machinery for Voight maximal orders in quaternion algebras over number fields.
-/

set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

@[expose] public section

namespace slop

open VoightMaximalOrder

section
-- Natural language: The regular trace bilinear form $T(x,y) = \operatorname{tr}_F(z \mapsto xyz)$
-- on a finite-dimensional $F$-algebra $B$ is defined to be the $F$-bilinear form $B \times B \to F$
-- given by $(x,y) \mapsto \tau(xy)$, where $\tau : B \to F$ is the composition of the
-- multiplication map $B \to \operatorname{End}_F(B)$ (sending $b$ to left-multiplication by $b$)
-- with the ordinary trace $\operatorname{tr}_F : \operatorname{End}_F(B) \to F$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The regular trace bilinear form on a finite-dimensional algebra. -/
@[nolint unusedArguments]
noncomputable def regTraceForm (F B : Type*) [Field F] [Ring B] [Algebra F B]
    [FiniteDimensional F B] : LinearMap.BilinForm F B :=
  let τ : B →ₗ[F] F := (LinearMap.trace F B).comp (LinearMap.mul F B)
  LinearMap.mk₂ F (fun x y => τ (x * y))
    (fun x₁ x₂ y => by simp [add_mul])
    (fun c x y => by simp)
    (fun x y₁ y₂ => by simp [mul_add])
    (fun c x y => by simp)


end

section
-- Natural language: Let $R$ be a commutative ring, $F$ a field, and $B$ a ring, together with an
-- algebra structure $R \to F$, an $R$-algebra structure on $B$, an $F$-algebra structure on $B$,
-- and a tower $R \to F \to B$ such that $F$ is the fraction field of $R$ and $B$ is
-- finite-dimensional over $F$.
-- If $O$ is an $R$-subalgebra of $B$ that is an $R$-order (i.e., $O$ is an $R$-lattice in $B$), and
-- $N$ is a Noetherian $R$-submodule of $B$ such that every $R$-subalgebra $O'$ of $B$ containing
-- $O$ and being an $R$-order has its underlying $R$-submodule contained in $N$, then there exists
-- an $R$-subalgebra $O'$ of $B$ containing $O$ that is a maximal $R$-order (i.e., maximal among
-- $R$-orders under inclusion).
-- Let $S$ be the set of subalgebras $O'$ of $B$ with $O \le O'$ and $O'.\text{submodule} \le N$.
-- The map sending $O' \in S$ to its underlying submodule (viewed as an element of the poset
-- $\operatorname{Iic}(N)$) is strictly monotone, and $\operatorname{Iic}(N)$ is well‑founded under
-- $>$ because $N$ is a Noetherian $R$-module; hence $S$ is well‑founded under $>$.
-- Since $O$ itself lies in $S$ (by the hypothesis $hbdd$), we may apply the well‑founded maximality
-- principle to the poset $S$ with the predicate “is an order”.
-- This yields a maximal element $m \in S$ above $O$ that is an order.
-- We claim $m$ is a maximal order above $O$: if $O''$ is any order with $m \le O''$, then $O \le
-- O''$ and $hbdd$ forces $O''.\text{submodule} \le N$, so $O'' \in S$; maximality of $m$ in $S$
-- then forces $O'' = m$, as required.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
@[nolint unusedArguments]
theorem exists_maximalOrder_ge_of_bddSubmodule
    (R F B : Type*) [CommRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Ring B] [Algebra R B] [Algebra F B]
    [IsScalarTower R F B] [FiniteDimensional F B]
    (O : Subalgebra R B) (hO : IsOrder R F B O)
    (N : Submodule R B) [IsNoetherian R N]
    (hbdd : ∀ O' : Subalgebra R B, O ≤ O' → IsOrder R F B O' → O'.toSubmodule ≤ N) :
    ∃ O' : Subalgebra R B, O ≤ O' ∧ IsMaximalOrder R F B O' := 
by
  -- Ambient type: orders-friendly subalgebras above O and bounded by N.
  set S : Set (Subalgebra R B) := {O' | O ≤ O' ∧ O'.toSubmodule ≤ N} with hS
  -- The map to submodules ≤ N, into Set.Iic N, is strictly monotone; target is WellFoundedGT.
  have hwf : WellFoundedGT S := by
    have hNoethIic : WellFoundedGT ↥(Set.Iic N) := by
      have : WellFoundedGT (Submodule R N) := wellFoundedGT
      exact (Submodule.mapIic N).symm.strictMono.wellFoundedGT
    have hmono : StrictMono (fun x : S => (⟨x.1.toSubmodule, x.2.2⟩ : ↥(Set.Iic N))) := by
      intro x y hxy
      have : x.1 < y.1 := hxy
      exact Subalgebra.toSubmodule.strictMono this
    exact hmono.wellFoundedGT
  -- O itself is in S.
  have hOS : O ∈ S := ⟨le_refl O, hbdd O (le_refl O) hO⟩
  -- Apply well-founded maximality above ⟨O, hOS⟩ with predicate "is an order".
  obtain ⟨m, hm_ge, hm_max⟩ :=
    exists_maximal_ge_of_wellFoundedGT (α := S) (fun x => IsOrder R F B x.1) ⟨O, hOS⟩ hO
  refine ⟨m.1, hm_ge, ?_⟩
  constructor
  · exact hm_max.1
  · intro O'' hO'' hmO''
    -- O'' is an order ≥ m.1 ≥ O, bounded by N, hence in S; use maximality.
    have hOO'' : O ≤ O'' := le_trans (le_trans hOS.1 hm_ge) hmO''
    have hO''N : O''.toSubmodule ≤ N := hbdd O'' hOO'' hO''
    have hmem : O'' ∈ S := ⟨hOO'', hO''N⟩
    have := hm_max.2 (y := ⟨O'', hmem⟩) hO'' (by exact hmO'')
    exact this



end

section
-- Natural language: Let $R$ be a commutative ring, $F$ a field, and $B$ a ring, together with an
-- $R$-algebra structure on $F$, an $F$-algebra structure on $B$, and an $R$-algebra structure on
-- $B$ such that the algebra structures are compatible (i.e., $\operatorname{IsScalarTower} R F B$),
-- and such that $B$ is finite-dimensional as an $F$-vector space. Assume also that $F$ is the
-- fraction field of $R$ (i.e., $\operatorname{IsFractionRing} R F$). Let $O$ be an $R$-subalgebra
-- of $B$ that is an $R$-order in $B$ (i.e., $\operatorname{IsOrder} R F B O$). Then every element
-- $x$ of $O$ is integral over $R$.
-- The proof uses the hypothesis that $O$ is an order in $B$ over $R$, which includes the condition
-- that $O$ is finitely generated as an $R$-module. From `hO.moduleFinite`, we obtain that the
-- underlying $R$-module of $O$ is finitely generated, which by `Module.Finite.iff_fg.mp` gives that
-- the submodule `Subalgebra.toSubmodule O` is finitely generated. Then the lemma
-- `IsIntegral.of_mem_of_fg` is applied with the subalgebra $O$, its finite generation, and the
-- element $x \in O$ to conclude that $x$ is integral over $R$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
@[nolint unusedArguments]
theorem mem_order_isIntegral
    (R F B : Type*) [CommRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Ring B] [Algebra R B] [Algebra F B]
    [IsScalarTower R F B] [FiniteDimensional F B]
    (O : Subalgebra R B) (hO : IsOrder R F B O) {x : B} (hx : x ∈ O) :
    IsIntegral R x := 
by
  have hfg : (Subalgebra.toSubmodule O).FG := Module.Finite.iff_fg.mp hO.moduleFinite
  exact IsIntegral.of_mem_of_fg O hfg x hx


end

section
-- Natural language: Let $R$ be a commutative ring, $F$ a field, and suppose $F$ is an $R$-algebra.
-- Let $\iota$ be a finite type with decidable equality, and let $M$ be an $\iota \times \iota$
-- matrix over $F$. If $M$ is integral over $R$, then the trace of $M$ is integral over $R$.
-- We consider two cases depending on whether the index type $\iota$ is empty. If $\iota$ is empty,
-- then $M.\text{trace}=0$ by definition, and $0$ is integral over $R$; this gives the result.
-- Otherwise, we base-change to the algebraic closure $\overline{F}$ of $F$: let
-- $\varphi:F\to\overline{F}$ be the algebra map, set $M' = M \operatorname{map} \varphi$, and note
-- that $M'$ is integral over $R$ because $M$ is and the map $\varphi.\text{mapMatrix}$ commutes
-- with the $R$-algebra structure. The characteristic polynomial of $M'$ is the image under
-- $\varphi$ of that of $M$, so it splits over $\overline{F}$ (since $\overline{F}$ is algebraically
-- closed) and is monic; its leading coefficient is $1$, hence integral over $R$. For any root
-- $x\in\overline{F}$ of $\operatorname{charpoly}(M')$, we have
-- $x\in\operatorname{spectum}_{\overline{F}}(M')$ by the spectral characterization of the
-- characteristic polynomial. Because $M'$ is integral over $R$, there exists a monic $q\in R[t]$
-- with $q(M')=0$; mapping $q$ to $\overline{F}[t]$ gives $q'(M')=0$, and then the spectral mapping
-- theorem forces $q'(x)=0$, so $x$ is a root of the monic $q$ and hence integral over $R$. Thus
-- every root of $\operatorname{charpoly}(M')$ is integral over $R$, and since the trace of $M'$
-- equals the negative of the second-highest coefficient of $\operatorname{charpoly}(M')$, it is
-- integral over $R$ by the lemma that coefficients of a monic polynomial whose roots are all
-- integral are themselves integral. Finally, $M'.\text{trace} = \varphi(M.\text{trace})$, and
-- because $\varphi$ is injective (as $\overline{F}$ is a faithful $F$-algebra), the integrality of
-- $\varphi(M.\text{trace})$ over $R$ implies that $M.\text{trace}$ is integral over $R$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
theorem isIntegral_trace_of_isIntegral
    (R F : Type*) [CommRing R] [Field F] [Algebra R F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι F}
    (hM : IsIntegral R M) : IsIntegral R M.trace := 
by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : M.trace = 0 := by
      simp [Matrix.trace, Matrix.diag]
    rw [h0]; exact isIntegral_zero
  · -- Base change to the algebraic closure of F.
    set AC := AlgebraicClosure F with hAC
    letI : Algebra F AC := inferInstance
    set φ : F →+* AC := algebraMap F AC with hφ
    set M' : Matrix ι ι AC := M.map φ with hM'def
    -- M' is integral over R, via the base-change ring hom on matrices.
    have hM'int : IsIntegral R M' := by
      have hcomm : (algebraMap R (Matrix ι ι AC)).comp (RingHom.id R)
          = φ.mapMatrix.comp (algebraMap R (Matrix ι ι F)) := by
        ext r i j
        simp only [RingHom.comp_apply, RingHom.id_apply, Matrix.algebraMap_matrix_apply,
          RingHom.mapMatrix_apply, Matrix.map_apply, apply_ite φ, map_zero]
        rw [hφ, ← IsScalarTower.algebraMap_apply R F AC]
      exact IsIntegral.map_of_comp_eq (RingHom.id R) φ.mapMatrix hcomm hM
    -- charpoly of M' splits and is monic.
    have hcp : M'.charpoly = M.charpoly.map φ := Matrix.charpoly_map M φ
    have hsplit : M'.charpoly.Splits := by
      rw [hcp]; exact IsAlgClosed.splits (M.charpoly.map φ)
    have hmonic : M'.charpoly.Monic := M'.charpoly_monic
    have hlead : IsIntegral R M'.charpoly.leadingCoeff := by
      rw [hmonic.leadingCoeff]; exact isIntegral_one
    -- Every root of M'.charpoly is integral over R.
    have hroots : ∀ x : AC, M'.charpoly.IsRoot x → IsIntegral R x := by
      intro x hx
      -- x is in the spectrum of M'.
      have hxspec : x ∈ spectrum AC M' := Matrix.mem_spectrum_of_isRoot_charpoly hx
      -- Obtain a monic annihilating polynomial q over R.
      obtain ⟨q, hqmon, hqeval⟩ := hM'int
      -- Map q to AC.
      set q' : Polynomial AC := q.map (algebraMap R AC) with hq'def
      have hq'eval : (Polynomial.aeval M') q' = 0 := by
        rw [hq'def, Polynomial.aeval_map_algebraMap]
        exact hqeval
      -- q'.eval x lies in the spectrum of aeval M' q' = 0, hence is 0.
      have hmem : q'.eval x ∈ spectrum AC ((Polynomial.aeval M') q') :=
        spectrum.subset_polynomial_aeval M' q' ⟨x, hxspec, rfl⟩
      rw [hq'eval, spectrum.zero_eq] at hmem
      have hzero : q'.eval x = 0 := by simpa using hmem
      -- Hence x is a root of the monic polynomial q, so integral over R.
      refine ⟨q, hqmon, ?_⟩
      rw [← Polynomial.eval_map]
      rw [hq'def] at hzero
      exact hzero
    -- Trace of M' = -charpoly coeff, integral over R.
    have htr' : IsIntegral R M'.trace := by
      rw [Matrix.trace_eq_neg_charpoly_coeff M']
      exact (Polynomial.isIntegral_coeff_of_factors M'.charpoly hlead hsplit hroots _).neg
    -- M'.trace = φ (M.trace).
    have htr_eq : M'.trace = φ (M.trace) := by
      simp only [hM'def, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    rw [htr_eq] at htr'
    exact (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective F AC)).mp htr'



end

section
-- Natural language: Let $R$ be a commutative ring which is an integrally closed domain, $F$ its
-- fraction field, and $B$ a ring which is an $R$-algebra, an $F$-algebra, and a finite-dimensional
-- $F$-vector space such that the $R$-algebra structure on $B$ factors through $F$ via the natural
-- map $R \to F$. If $z \in B$ is integral over $R$, then the trace $\operatorname{tr}_F(w \mapsto
-- zw)$ lies in the image of $R$ in $F$.
-- We choose an $F$-basis $b$ of $B$ and consider the matrix $M = (\text{Algebra.leftMulMatrix } b)
-- z$ representing left multiplication by $z$ in this basis. Since $z$ is integral over $R$, the map
-- $(\text{Algebra.leftMulMatrix } b) \circ z$ is also integral over $R$ (as a homomorphism of
-- $R$-algebras), so $M$ is integral over $R$. The trace of $\text{mulLeft } z$ as an $F$-linear
-- endomorphism of $B$ equals the matrix trace of $M$, by the standard relation between the trace of
-- an endomorphism and the trace of its matrix in a basis. Hence $\text{trace}_F(\text{mulLeft } z)
-- = \text{trace}(M)$. By the lemma `isIntegral_trace_of_isIntegral`, the trace of an integral
-- matrix is integral over $R$, so $\text{trace}_F(\text{mulLeft } z)$ is integral over $R$. Because
-- $R$ is integrally closed in its fraction field $F$, every element of $F$ integral over $R$ lies
-- in the image of $R \to F$; therefore $\text{trace}_F(\text{mulLeft } z)$ belongs to
-- $\text{algebraMap } R \, F$’s range.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
@[nolint unusedArguments]
theorem isIntegral_regTrace_mem_range
    (R F B : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field F]
    [Algebra R F] [IsFractionRing R F] [Ring B] [Algebra R B] [Algebra F B]
    [IsScalarTower R F B] [FiniteDimensional F B] {z : B} (hz : IsIntegral R z) :
    (LinearMap.trace F B) (LinearMap.mulLeft F z) ∈ (algebraMap R F).range := 
by
  rw [RingHom.mem_range]
  classical
  -- Choose an F-basis of B.
  set b := Module.finBasis F B with hb
  -- The left-multiplication matrix of z is integral over R.
  have hMint : IsIntegral R ((Algebra.leftMulMatrix b) z) :=
    hz.map ((Algebra.leftMulMatrix b).restrictScalars R)
  -- The regular trace equals the matrix trace of the left-mult matrix.
  have htr_eq : (LinearMap.trace F B) (LinearMap.mulLeft F z)
      = ((Algebra.leftMulMatrix b) z).trace := by
    rw [LinearMap.trace_eq_matrix_trace F b, Algebra.toMatrix_lmul_eq]
  -- Hence the trace is integral over R.
  have hkey : IsIntegral R ((LinearMap.trace F B) (LinearMap.mulLeft F z)) := by
    rw [htr_eq]
    exact isIntegral_trace_of_isIntegral R F hMint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hkey
  exact ⟨y, hy⟩



end

section
-- Natural language: Let $R$ be a Noetherian integrally closed domain with fraction field $F$, and
-- $B$ a finite-dimensional $F$-algebra whose regular trace form is nondegenerate. Then every
-- $R$-order $O$ in $B$ is contained in a maximal $R$-order.
-- Given that $O$ spans $B$ over $F$ (by $hO.\text{spans}$), we extract an $F$-basis $e$ of $B$
-- contained in $O$ using `Module.Basis.ofSpan`.
-- Let $N$ be the dual submodule of $\operatorname{span}_R(\operatorname{range} e)$ with respect to
-- the regular trace form; $N$ is finitely generated because it is the dual of a span of a finite
-- set, hence $N$ is Noetherian over $R$.
-- For any order $O' \supseteq O$, we show $O' \subseteq N$: if $x \in O'$ and $y \in
-- \operatorname{span}_R(\operatorname{range} e)$, then $y \in O$ (since the basis lies in $O$) and
-- thus $y \in O'$; then $xy \in O'$, so $xy$ is integral over $R$ by `mem_order_isIntegral`, and
-- therefore $\operatorname{tr}_{B/F}(\operatorname{mul}_F(xy))$ lies in the image of $R$ in $F$ by
-- `isIntegral_regTrace_mem_range`; this shows $(x,y)$ lies in the dual submodule, i.e. $x \in N$.
-- Thus $N$ is a Noetherian $R$-submodule that bounds every order containing $O$, so the abstract
-- lemma `exists_maximalOrder_ge_of_bddSubmodule` yields a maximal order $O' \ge O$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
theorem exists_maximalOrder_ge_generic
    (R F B : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Ring B] [Algebra R B] [Algebra F B]
    [IsScalarTower R F B] [FiniteDimensional F B]
    (hnd : (regTraceForm F B).Nondegenerate)
    (O : Subalgebra R B) (hO : IsOrder R F B O) :
    ∃ O' : Subalgebra R B, O ≤ O' ∧ IsMaximalOrder R F B O' := 
by
  classical
  -- O spans B over F.
  have hspanO : (⊤ : Submodule F B) ≤ Submodule.span F (O : Set B) := by
    have := hO.spans
    simp only [Subalgebra.coe_toSubmodule] at this
    rw [this]
  -- Extract an F-basis of B contained in O.
  set e := Module.Basis.ofSpan hspanO with he
  have he_sub : Set.range ⇑e ⊆ (O : Set B) := Module.Basis.ofSpan_subset hspanO
  haveI := FiniteDimensional.fintypeBasisIndex e
  -- The bounding submodule: the dual of the R-span of the basis.
  set N : Submodule R B := (regTraceForm F B).dualSubmodule (Submodule.span R (Set.range ⇑e)) with hN
  -- N is finitely generated (dual of span of a basis), hence Noetherian over Noetherian R.
  have hNfg : N.FG := by
    rw [hN, (regTraceForm F B).dualSubmodule_span_of_basis hnd e]
    exact Submodule.fg_span (Set.finite_range _)
  haveI : IsNoetherian R N := isNoetherian_of_fg_of_noetherian N hNfg
  -- Every order O' ⊇ O has underlying submodule ≤ N.
  have hbdd : ∀ O' : Subalgebra R B, O ≤ O' → IsOrder R F B O' → O'.toSubmodule ≤ N := by
    intro O' hOO' hO' x hx
    rw [hN, LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    -- y ∈ span R (range e) ⊆ O ⊆ O'; x ∈ O'; so x*y ∈ O', integral, trace ∈ R.
    have hyO' : y ∈ O' := by
      have : Submodule.span R (Set.range ⇑e) ≤ O'.toSubmodule := by
        rw [Submodule.span_le]
        exact le_trans he_sub hOO'
      exact this hy
    have hxO' : x ∈ O' := hx
    have hxy : x * y ∈ O' := O'.mul_mem hxO' hyO'
    have hint : IsIntegral R (x * y) := mem_order_isIntegral R F B O' hO' hxy
    -- regTraceForm x y = trace (mulLeft F (x*y)).
    have hval : (regTraceForm F B) x y
        = (LinearMap.trace F B) (LinearMap.mulLeft F (x * y)) := by
      rfl
    rw [hval, Submodule.mem_one]
    exact RingHom.mem_range.mp (isIntegral_regTrace_mem_range R F B hint)
  -- Apply the abstract bridge.
  exact exists_maximalOrder_ge_of_bddSubmodule R F B O hO N hbdd



end

section
-- Natural language: For a field $K$, elements $a,b \in K$, and a quaternion $z \in
-- \mathbb{H}[K,a,0,b]$, the trace of the linear map of left multiplication by $z$ on
-- $\mathbb{H}[K,a,0,b]$ equals $4$ times the real part $z_{\mathrm{re}}$.
-- We work over a field \(K\) and consider the quaternion algebra \(\mathbb{H}[K, a, 0, b]\) with
-- its standard basis \(\{\mathbf{1}, \mathbf{i}, \mathbf{j}, \mathbf{k}\}\) given by `basisOneIJK`.
-- First we note two facts about this basis: for any basis vectors \(e_i, e_j\) we have
-- \(\operatorname{repr}(e_i)(e_j) = \delta_{ij}\) (the Kronecker delta), and the components of each
-- basis vector are exactly one in the coordinate corresponding to its index and zero elsewhere.
-- Using these, we rewrite the trace of left multiplication by an element \(z\) as the matrix trace
-- of the \(4\times4\) matrix representing \(\operatorname{mulLeft}(z)\) in this basis.
-- We expand the matrix entries via the multiplication rules of the quaternion algebra (the formulas
-- for \(\operatorname{re}(z\cdot e_j)\), \(\operatorname{imI}(z\cdot e_j)\), etc.), substitute the
-- component values of the basis vectors, and evaluate the four diagonal entries.
-- After simplifying the many case splits (each index \(i\) yields a sum of four terms, most of
-- which vanish because the basis vectors have only one nonzero component), we obtain the sum
-- \(4\cdot z.\mathrm{re}\).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
open scoped Quaternion in
theorem trace_mulLeft_quaternion (K : Type*) [Field K] (a b : K)
    (z : ℍ[K, a, 0, b]) :
    (LinearMap.trace K ℍ[K, a, 0, b]) (LinearMap.mulLeft K z) = 4 * z.re := 
by
  classical
  have hbc : ∀ (i j : Fin 4),
      ((QuaternionAlgebra.basisOneIJK a 0 b).repr (QuaternionAlgebra.basisOneIJK a 0 b i)) j
        = (if i = j then (1 : K) else 0) := by
    intro i j
    rw [Module.Basis.repr_self, Finsupp.single_apply]
  have hcomp : ∀ i : Fin 4,
      (QuaternionAlgebra.basisOneIJK a 0 b i).re = (if i = 0 then (1:K) else 0)
      ∧ (QuaternionAlgebra.basisOneIJK a 0 b i).imI = (if i = 1 then (1:K) else 0)
      ∧ (QuaternionAlgebra.basisOneIJK a 0 b i).imJ = (if i = 2 then (1:K) else 0)
      ∧ (QuaternionAlgebra.basisOneIJK a 0 b i).imK = (if i = 3 then (1:K) else 0) := by
    intro i
    have h := QuaternionAlgebra.coe_basisOneIJK_repr a 0 b (QuaternionAlgebra.basisOneIJK a 0 b i)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := (congrFun h 0).symm; rw [hbc i 0] at this; simpa using this
    · have := (congrFun h 1).symm; rw [hbc i 1] at this; simpa using this
    · have := (congrFun h 2).symm; rw [hbc i 2] at this; simpa using this
    · have := (congrFun h 3).symm; rw [hbc i 3] at this; simpa using this
  rw [LinearMap.trace_eq_matrix_trace K (QuaternionAlgebra.basisOneIJK a 0 b)]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four, LinearMap.toMatrix_apply,
    LinearMap.mulLeft_apply, QuaternionAlgebra.coe_basisOneIJK_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons,
    QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  simp only [(hcomp 0).1, (hcomp 0).2.1, (hcomp 0).2.2.1, (hcomp 0).2.2.2,
    (hcomp 1).1, (hcomp 1).2.1, (hcomp 1).2.2.1, (hcomp 1).2.2.2,
    (hcomp 2).1, (hcomp 2).2.1, (hcomp 2).2.2.1, (hcomp 2).2.2.2,
    (hcomp 3).1, (hcomp 3).2.1, (hcomp 3).2.2.1, (hcomp 3).2.2.2]
  simp only [Fin.reduceEq, if_true, if_false, reduceIte]
  ring



end

section
-- Natural language: For a number field $K$ and elements $a,b \in K$ with $a \neq 0$ and $b \neq 0$,
-- the regular trace form on the quaternion algebra $\mathbb{H}[K,a,0,b]$ is nondegenerate.
-- The proof first applies the criterion that a bilinear form is nondegenerate if its matrix with
-- respect to some basis has nonzero determinant, using the basis `QuaternionAlgebra.basisOneIJK a 0
-- b`.
-- It computes the components of each basis vector under the quaternion representation, showing that
-- for each index `i` the tuple `(re, imI, imJ, imK)` of the `i`-th basis vector is the standard
-- basis vector of `K^4`.
-- Using the formula `regTraceForm x y = 4 * (x * y).re` (which follows from the definition of the
-- regular trace form and the lemma `trace_mulLeft_quaternion`), the entry of the Gram matrix at
-- position `(i,j)` becomes `4 * ((B i) * (B j)).re`.
-- By expanding the product via the component formulas, one finds that the Gram matrix is diagonal
-- with entries `4, 4a, 4b, -(4ab)` along the diagonal.
-- The determinant is therefore the product of these four entries.
-- Since `a ≠ 0` and `b ≠ 0` and `4 ≠ 0` in `K` (because `K` is a number field, hence of
-- characteristic zero), each factor is nonzero, so the product is nonzero, establishing
-- nondegeneracy.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
open scoped NumberField Quaternion in
theorem regTraceForm_nondegenerate (K : Type*) [Field K] [NumberField K] (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (regTraceForm K ℍ[K, a, 0, b]).Nondegenerate := 
by
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero (regTraceForm K ℍ[K, a, 0, b])
    (QuaternionAlgebra.basisOneIJK a 0 b)
  -- Abbreviation for basis
  set B := QuaternionAlgebra.basisOneIJK a 0 b with hB
  -- Components of each basis vector via repr
  have hcomp : ∀ (i j : Fin 4),
      (![(B i).re, (B i).imI, (B i).imJ, (B i).imK] : Fin 4 → K) j
        = if i = j then 1 else 0 := by
    intro i j
    rw [hB, ← QuaternionAlgebra.coe_basisOneIJK_repr]
    rw [Module.Basis.repr_self_apply]
  -- Extract individual components
  have cre : ∀ i, (B i).re = (if i = (0 : Fin 4) then 1 else 0) := by
    intro i; have := hcomp i 0; simpa using this
  have ciI : ∀ i, (B i).imI = (if i = (1 : Fin 4) then 1 else 0) := by
    intro i; have := hcomp i 1; simpa using this
  have ciJ : ∀ i, (B i).imJ = (if i = (2 : Fin 4) then 1 else 0) := by
    intro i; have := hcomp i 2; simpa using this
  have ciK : ∀ i, (B i).imK = (if i = (3 : Fin 4) then 1 else 0) := by
    intro i; have := hcomp i 3; simpa using this
  -- Entry formula
  have hentry : ∀ (x y : ℍ[K, a, 0, b]),
      (regTraceForm K ℍ[K, a, 0, b]) x y = 4 * (x * y).re := by
    intro x y
    have h : (regTraceForm K ℍ[K, a, 0, b]) x y
        = (LinearMap.trace K ℍ[K, a, 0, b]) (LinearMap.mulLeft K (x * y)) := rfl
    rw [h, trace_mulLeft_quaternion K a b (x * y)]
  -- The Gram matrix equals a diagonal matrix
  have hM : (LinearMap.BilinForm.toMatrix B) (regTraceForm K ℍ[K, a, 0, b])
      = Matrix.diagonal ![4, 4 * a, 4 * b, -(4 * a * b)] := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, hentry, QuaternionAlgebra.re_mul,
      cre i, ciI i, ciJ i, ciK i, cre j, ciI j, ciJ j, ciK j]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal] <;> ring
  rw [hM, Matrix.det_diagonal]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  -- Now goal: 4 * (4*a) * (4*b) * (-(4*a*b)) ≠ 0
  have h4 : (4 : K) ≠ 0 := by norm_num
  have : (4 : K) * (4 * a) * (4 * b) * -(4 * a * b) ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero h4
    · exact mul_ne_zero h4 ha
    · exact mul_ne_zero h4 hb
    · simp only [neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero h4 ha) hb
  convert this using 2



end

section
-- Natural language: Let $K$ be a number field with ring of integers $\mathcal{O}_K$, let $a, b \in
-- K$ with $a \neq 0$ and $b \neq 0$, and let $\mathbb{H}[K, a, 0, b]$ be the associated quaternion
-- algebra over $K$. Then for every $\mathcal{O}_K$-subalgebra $O$ of $\mathbb{H}[K, a, 0, b]$ that
-- is an $\mathcal{O}_K$-order in $\mathbb{H}[K, a, 0, b]$ (i.e., satisfies
-- $\operatorname{IsOrder}(\mathcal{O}_K, K, \mathbb{H}[K, a, 0, b], O)$), there exists an
-- $\mathcal{O}_K$-subalgebra $O'$ of $\mathbb{H}[K, a, 0, b]$ such that $O'$ is a maximal
-- $\mathcal{O}_K$-order in $\mathbb{H}[K, a, 0, b]$ (i.e., satisfies
-- $\operatorname{IsMaximalOrder}(\mathcal{O}_K, K, \mathbb{H}[K, a, 0, b], O')$) and $O \subseteq
-- O'$.
-- Let $O \subseteq B$ be an $R$-order. If $O$ is maximal, take $O' = O$. Otherwise, there exists an
-- $R$-order $O_2 \supsetneq O$; by Lemma 15.5.1 the discriminant ideal strictly increases,
-- $\operatorname{disc}(O) \subsetneq \operatorname{disc}(O_2)$. Iterating, we obtain an ascending
-- chain of $R$-orders $O = O_1 \subsetneq O_2 \subsetneq \cdots$ with strictly ascending
-- discriminant ideals $\operatorname{disc}(O_1) \subsetneq \operatorname{disc}(O_2) \subsetneq
-- \cdots$ in $R$. Since $R$ is noetherian, this ascending chain of ideals stabilizes after finitely
-- many steps; the terminal order $O'$ of the chain then admits no proper $R$-order superorder and
-- hence is maximal by Lemma 15.2.15, while $O \subseteq O'$ by construction. (Cf. Proposition
-- 15.5.2.)
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
open scoped NumberField Quaternion in
theorem exists_maximalOrder_ge (K : Type*) [Field K] [NumberField K] (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (O : Subalgebra (𝓞 K) ℍ[K, a, 0, b])
    (hO : IsOrder (𝓞 K) K ℍ[K, a, 0, b] O) :
    ∃ O' : Subalgebra (𝓞 K) ℍ[K, a, 0, b],
      IsMaximalOrder (𝓞 K) K ℍ[K, a, 0, b] O' ∧ O ≤ O' := 
by
  obtain ⟨O', hle, hmax⟩ := exists_maximalOrder_ge_generic (𝓞 K) K ℍ[K, a, 0, b]
    (regTraceForm_nondegenerate K a b ha hb) O hO
  exact ⟨O', hmax, hle⟩



end

section
-- Natural language: For a number field $K$ and $a,b \in K$ with $a \neq 0$ and $b \neq 0$, there
-- exists an $\mathcal{O}_K$-subalgebra $O$ of the quaternion algebra $\mathbb{H}[K,a,0,b]$ that is
-- an $\mathcal{O}_K$-order in $\mathbb{H}[K,a,0,b]$.
-- Given nonzero elements \(a,b\) in a number field \(K\), we construct an \(\mathfrak{O}_K\)-order
-- in the quaternion algebra \(\mathbb{H}[K,a,0,b]\).
-- First, using that \(K\) is the fraction field of \(\mathfrak{O}_K\), write \(a = x_a / y_a\) and
-- \(b = x_b / y_b\) with \(x_a,y_a,x_b,y_b \in \mathfrak{O}_K\) and \(y_a,y_b\) nonzero; then
-- \((y_a : K) a = (x_a : K)\) and similarly for \(b\).
-- Set \(c_a = (y_a : K)\), \(d_a = (y_b : K)\) and define three quaternions
-- \(q_1 = (0,c_a,0,0)\), \(q_2 = (0,0,d_a,0)\), \(q_3 = (0,0,0,c_a d_a)\).
-- Let \(s = \{1,q_1,q_2,q_3\}\).
-- Using the explicit multiplication formulas for quaternions and the field identities, one computes
-- all pairwise products of the generators: each product is an \(\mathfrak{O}_K\)-multiple of one of
-- the generators (e.g., \(q_1^2 = (y_a x_a)\cdot 1\), \(q_1 q_2 = q_3\), \(q_2 q_1 = (-1)\cdot
-- q_3\), etc.).
-- Hence every product of two elements of \(s\) lies in the \(\mathfrak{O}_K\)-span of \(s\).
-- By a double induction using the submodule span axioms, this implies that the
-- \(\mathfrak{O}_K\)-span of \(s\) is closed under multiplication; together with containing \(1\)
-- it forms an \(\mathfrak{O}_K\)-subalgebra \(O\).
-- The set \(s\) is finite, so \(O\) is finitely generated as an \(\mathfrak{O}_K\)-module, i.e., an
-- order.
-- To see that \(O\) spans \(\mathbb{H}[K,a,0,b]\) over \(K\), note that the standard basis
-- \(\{1,i,j,k\}\) can be expressed as \(K\)-multiples of the generators:
-- \(i = c_a^{-1} q_1\), \(j = d_a^{-1} q_2\), \(k = (c_a d_a)^{-1} q_3\), and \(1\) is already in
-- \(s\).
-- Since every quaternion is a \(K\)-linear combination of \(1,i,j,k\), it lies in the \(K\)-span of
-- \(s\), which equals the \(K\)-span of \(O\).
-- Thus \(O\) is an \(\mathfrak{O}_K\)-order in \(\mathbb{H}[K,a,0,b]\).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
open scoped NumberField Quaternion in
@[nolint unusedArguments]
theorem exists_order (K : Type*) [Field K] [NumberField K] (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ O : Subalgebra (𝓞 K) ℍ[K, a, 0, b], IsOrder (𝓞 K) K ℍ[K, a, 0, b] O := 
by
  classical
  haveI : SMulCommClass (𝓞 K) ℍ[K,a,0,b] ℍ[K,a,0,b] := Algebra.to_smulCommClass
  haveI : IsScalarTower (𝓞 K) ℍ[K,a,0,b] ℍ[K,a,0,b] := IsScalarTower.right
  -- Get integer denominators: c,d ∈ 𝓞K nonzero with c^2 a, d^2 b integral.
  -- From a = xa/ya  ⟹  ya • a = algebraMap xa, i.e. (ya:K) * a = (xa:K).
  obtain ⟨xa, ya, hya, hxya⟩ := IsFractionRing.div_surjective (𝓞 K) (K := K) a
  obtain ⟨xb, yb, hyb, hxyb⟩ := IsFractionRing.div_surjective (𝓞 K) (K := K) b
  -- ya ≠ 0, yb ≠ 0
  have hya0 : ya ≠ 0 := nonZeroDivisors.ne_zero hya
  have hyb0 : yb ≠ 0 := nonZeroDivisors.ne_zero hyb
  -- key field identities: (ya:K)*a = (xa:K), (yb:K)*b = (xb:K)
  have hdena : (algebraMap (𝓞 K) K) ya ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hya0
  have hdenb : (algebraMap (𝓞 K) K) yb ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hyb0
  have keya : (algebraMap (𝓞 K) K ya) * a = algebraMap (𝓞 K) K xa := by
    field_simp at hxya; exact hxya.symm
  have keyb : (algebraMap (𝓞 K) K yb) * b = algebraMap (𝓞 K) K xb := by
    field_simp at hxyb; exact hxyb.symm
  set ca : K := algebraMap (𝓞 K) K ya with hca
  set da : K := algebraMap (𝓞 K) K yb with hda
  -- generators
  set q1 : ℍ[K,a,0,b] := ⟨0, ca, 0, 0⟩ with hq1
  set q2 : ℍ[K,a,0,b] := ⟨0, 0, da, 0⟩ with hq2
  set q3 : ℍ[K,a,0,b] := ⟨0, 0, 0, ca * da⟩ with hq3
  set s : Set ℍ[K,a,0,b] := {1, q1, q2, q3} with hs
  have hsfin : s.Finite := by
    rw [hs]; exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _
  -- membership helpers
  have hmem1 : (1 : ℍ[K,a,0,b]) ∈ Submodule.span (𝓞 K) s :=
    Submodule.subset_span (by rw [hs]; simp)
  have hmemq1 : q1 ∈ Submodule.span (𝓞 K) s :=
    Submodule.subset_span (by rw [hs]; simp)
  have hmemq2 : q2 ∈ Submodule.span (𝓞 K) s :=
    Submodule.subset_span (by rw [hs]; simp)
  have hmemq3 : q3 ∈ Submodule.span (𝓞 K) s :=
    Submodule.subset_span (by rw [hs]; simp)
  -- smul action of 𝓞K on ℍ: (r • x) computes componentwise via ca-style algebraMap
  have hsmulOK : ∀ (r : 𝓞 K) (x : ℍ[K,a,0,b]), r • x = (algebraMap (𝓞 K) K r) • x := by
    intro r x; rw [algebra_compatible_smul K r x]
  -- q1*q1 = (ya*xa) • 1
  have e11 : q1 * q1 = (ya * xa) • (1 : ℍ[K,a,0,b]) := by
    rw [hsmulOK, hq1, QuaternionAlgebra.mk_mul_mk]
    rw [show (1 : ℍ[K,a,0,b]) = (⟨1,0,0,0⟩ : ℍ[K,a,0,b]) from rfl,
      QuaternionAlgebra.smul_mk]
    ext <;> simp
    · simp only [← hca, ← hda, ← keya, ← keyb]; ring
  have e22 : q2 * q2 = (yb * xb) • (1 : ℍ[K,a,0,b]) := by
    rw [hsmulOK, hq2, QuaternionAlgebra.mk_mul_mk]
    rw [show (1 : ℍ[K,a,0,b]) = (⟨1,0,0,0⟩ : ℍ[K,a,0,b]) from rfl,
      QuaternionAlgebra.smul_mk]
    ext <;> simp
    · simp only [← hca, ← hda, ← keya, ← keyb]; ring
  have e12 : q1 * q2 = q3 := by
    rw [hq1, hq2, hq3, QuaternionAlgebra.mk_mul_mk]; ext <;> simp
  have e21 : q2 * q1 = (-1 : 𝓞 K) • q3 := by
    rw [hsmulOK, hq2, hq1, hq3, QuaternionAlgebra.mk_mul_mk,
      QuaternionAlgebra.smul_mk]
    ext <;> simp <;> ring
  have e13 : q1 * q3 = (ya * xa) • q2 := by
    rw [hsmulOK, hq1, hq3, hq2, QuaternionAlgebra.mk_mul_mk,
      QuaternionAlgebra.smul_mk]
    ext <;> simp
    · simp only [← hca, ← hda, ← keya, ← keyb]; ring
  have e31 : q3 * q1 = (-(ya * xa)) • q2 := by
    rw [hsmulOK, hq3, hq1, hq2, QuaternionAlgebra.mk_mul_mk,
      QuaternionAlgebra.smul_mk]
    ext <;> simp
    · simp only [← hca, ← hda, ← keya, ← keyb]; ring
  have e23 : q2 * q3 = (-(yb * xb)) • q1 := by
    rw [hsmulOK, hq2, hq3, hq1, QuaternionAlgebra.mk_mul_mk,
      QuaternionAlgebra.smul_mk]
    ext <;> simp
    · simp only [← hca, ← hda, ← keya, ← keyb]; ring
  have e32 : q3 * q2 = (yb * xb) • q1 := by
    rw [hsmulOK, hq3, hq2, hq1, QuaternionAlgebra.mk_mul_mk,
      QuaternionAlgebra.smul_mk]
    ext <;> simp
    · simp only [← hca, ← hda, ← keya, ← keyb]; ring
  have e33 : q3 * q3 = (-(ya * xa * (yb * xb))) • (1 : ℍ[K,a,0,b]) := by
    rw [hsmulOK, hq3, QuaternionAlgebra.mk_mul_mk]
    rw [show (1 : ℍ[K,a,0,b]) = (⟨1,0,0,0⟩ : ℍ[K,a,0,b]) from rfl,
      QuaternionAlgebra.smul_mk]
    ext <;> simp
    · simp only [← hca, ← hda, ← keya, ← keyb]; ring
  -- membership of each product in the span
  have m11 : q1 * q1 ∈ Submodule.span (𝓞 K) s := by rw [e11]; exact Submodule.smul_mem _ _ hmem1
  have m22 : q2 * q2 ∈ Submodule.span (𝓞 K) s := by rw [e22]; exact Submodule.smul_mem _ _ hmem1
  have m12 : q1 * q2 ∈ Submodule.span (𝓞 K) s := by rw [e12]; exact hmemq3
  have m21 : q2 * q1 ∈ Submodule.span (𝓞 K) s := by rw [e21]; exact Submodule.smul_mem _ _ hmemq3
  have m13 : q1 * q3 ∈ Submodule.span (𝓞 K) s := by rw [e13]; exact Submodule.smul_mem _ _ hmemq2
  have m31 : q3 * q1 ∈ Submodule.span (𝓞 K) s := by rw [e31]; exact Submodule.smul_mem _ _ hmemq2
  have m23 : q2 * q3 ∈ Submodule.span (𝓞 K) s := by rw [e23]; exact Submodule.smul_mem _ _ hmemq1
  have m32 : q3 * q2 ∈ Submodule.span (𝓞 K) s := by rw [e32]; exact Submodule.smul_mem _ _ hmemq1
  have m33 : q3 * q3 ∈ Submodule.span (𝓞 K) s := by rw [e33]; exact Submodule.smul_mem _ _ hmem1
  -- generator*generator ⊆ span s
  have hgen : ∀ p ∈ s, ∀ q ∈ s, p * q ∈ Submodule.span (𝓞 K) s := by
    intro p hp q hq
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      (try simp only [one_mul, mul_one]) <;>
      first
        | exact hmem1 | exact hmemq1 | exact hmemq2 | exact hmemq3
        | exact m11 | exact m12 | exact m13 | exact m21 | exact m22 | exact m23
        | exact m31 | exact m32 | exact m33
  -- closure under multiplication via double span induction
  have hclosed : ∀ x y : ℍ[K,a,0,b], x ∈ Submodule.span (𝓞 K) s →
      y ∈ Submodule.span (𝓞 K) s → x * y ∈ Submodule.span (𝓞 K) s := by
    intro x y hx hy
    induction hx using Submodule.span_induction with
    | mem p hp =>
        induction hy using Submodule.span_induction with
        | mem q hq => exact hgen p hp q hq
        | zero => rw [mul_zero]; exact Submodule.zero_mem _
        | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
        | smul r u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hu
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
    | smul r u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu
  -- Define the order
  set O : Subalgebra (𝓞 K) ℍ[K,a,0,b] :=
    (Submodule.span (𝓞 K) s).toSubalgebra hmem1 hclosed with hO
  refine ⟨O, ?_, ?_⟩
  · -- module finite
    have hOtoM : Subalgebra.toSubmodule O = Submodule.span (𝓞 K) s := by
      rw [hO, Submodule.toSubalgebra_toSubmodule]
    rw [hOtoM]
    exact Module.Finite.iff_fg.2 (Submodule.fg_span hsfin)
  · -- spans over K
    have hOtoM : Subalgebra.toSubmodule O = Submodule.span (𝓞 K) s := by
      rw [hO, Submodule.toSubalgebra_toSubmodule]
    rw [show (↑(Subalgebra.toSubmodule O) : Set ℍ[K,a,0,b])
        = ↑(Submodule.span (𝓞 K) s) from congrArg _ hOtoM,
      Submodule.span_span_of_tower (𝓞 K) K]
    have hsub : s ⊆ (↑(Submodule.span K s) : Set ℍ[K,a,0,b]) := Submodule.subset_span
    have hmemK1 : (1 : ℍ[K,a,0,b]) ∈ Submodule.span K s := hsub (by rw [hs]; simp)
    have hmemKq1 : q1 ∈ Submodule.span K s := hsub (by rw [hs]; simp)
    have hmemKq2 : q2 ∈ Submodule.span K s := hsub (by rw [hs]; simp)
    have hmemKq3 : q3 ∈ Submodule.span K s := hsub (by rw [hs]; simp)
    have hi : (⟨0,1,0,0⟩ : ℍ[K,a,0,b]) ∈ Submodule.span K s := by
      have hval : (⟨0,1,0,0⟩ : ℍ[K,a,0,b]) = (ca⁻¹) • q1 := by
        rw [hq1, QuaternionAlgebra.smul_mk]
        ext <;> simp <;> field_simp
      rw [hval]; exact Submodule.smul_mem _ _ hmemKq1
    have hj : (⟨0,0,1,0⟩ : ℍ[K,a,0,b]) ∈ Submodule.span K s := by
      have hval : (⟨0,0,1,0⟩ : ℍ[K,a,0,b]) = (da⁻¹) • q2 := by
        rw [hq2, QuaternionAlgebra.smul_mk]
        ext <;> simp <;> field_simp
      rw [hval]; exact Submodule.smul_mem _ _ hmemKq2
    have hk : (⟨0,0,0,1⟩ : ℍ[K,a,0,b]) ∈ Submodule.span K s := by
      have hcd : ca * da ≠ 0 := mul_ne_zero hdena hdenb
      have hval : (⟨0,0,0,1⟩ : ℍ[K,a,0,b]) = ((ca * da)⁻¹) • q3 := by
        rw [hq3, QuaternionAlgebra.smul_mk]
        ext <;> simp <;> field_simp
      rw [hval]; exact Submodule.smul_mem _ _ hmemKq3
    rw [eq_top_iff]
    rintro x -
    have hxdecomp : x = x.re • (1 : ℍ[K,a,0,b]) + x.imI • (⟨0,1,0,0⟩ : ℍ[K,a,0,b])
        + x.imJ • (⟨0,0,1,0⟩ : ℍ[K,a,0,b]) + x.imK • (⟨0,0,0,1⟩ : ℍ[K,a,0,b]) := by
      ext <;> simp
    rw [hxdecomp]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ hmemK1) (Submodule.smul_mem _ _ hi))
      (Submodule.smul_mem _ _ hj)) (Submodule.smul_mem _ _ hk)



end

section
-- Natural language: Let $K$ be a number field with ring of integers $\mathcal{O}_K$, let $a, b \in
-- K$ with $a \neq 0$ and $b \neq 0$, and let $\mathbb{H}[K, a, 0, b]$ be the associated quaternion
-- algebra over $K$. Then there exists a subalgebra $O$ of $\mathbb{H}[K, a, 0, b]$ over
-- $\mathcal{O}_K$ such that $O$ is a maximal $\mathcal{O}_K$-order in $\mathbb{H}[K, a, 0, b]$.
-- By Lemma 10.2.5 (the left order of a lattice), $B$ has at least one $R$-order $O$, obtained as
-- the left order of an $R$-lattice, e.g.\ the $R$-span of a $K$-basis of $B$. Consider the
-- collection of $R$-orders containing $O$. If $O$ is maximal, we are done. Otherwise there exists
-- an $R$-order $O' \supsetneq O$. By Lemma 15.5.1, a strict containment of orders gives a strict
-- containment of discriminant ideals $\operatorname{disc}(O') \supsetneq \operatorname{disc}(O)$;
-- equivalently, since $\operatorname{disc}(O) = [O' : O]_R^2 \operatorname{disc}(O')$, the index
-- strictly decreases. Iterating produces an ascending chain of orders $O = O_1 \subsetneq O_2
-- \subsetneq \cdots$ and a strictly ascending chain of discriminant ideals
-- $\operatorname{disc}(O_1) \subsetneq \operatorname{disc}(O_2) \subsetneq \cdots$ in $R$. Since
-- $R$ is noetherian, this chain stabilizes after finitely many steps, and the resulting order is
-- maximal by Lemma 15.2.15. (Cf. Proposition 15.5.2.)
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
open scoped NumberField Quaternion in
theorem exists_maximalOrder (K : Type*) [Field K] [NumberField K] (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ O : Subalgebra (𝓞 K) ℍ[K, a, 0, b],
      IsMaximalOrder (𝓞 K) K ℍ[K, a, 0, b] O := 
by
  obtain ⟨O, hO⟩ := exists_order K a b ha hb
  obtain ⟨O', _hle, hmax⟩ := exists_maximalOrder_ge_generic (𝓞 K) K ℍ[K, a, 0, b]
    (regTraceForm_nondegenerate K a b ha hb) O hO
  exact ⟨O', hmax⟩



end



end slop
