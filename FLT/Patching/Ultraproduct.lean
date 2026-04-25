module

public import FLT.Patching.Utils.Lemmas
public import FLT.Patching.Utils.StructureFiniteness

@[expose] public section

/- TODO: replace this with ultraproduct in mathlib -/

set_option autoImplicit false
variable (R₀ : Type*) [CommRing R₀]
variable {ι : Type*} {R M : ι → Type*} [∀ i, CommRing (R i)] [∀ i, AddCommGroup (M i)]
variable [∀ i, Algebra R₀ (R i)] [∀ i, Module (R i) (M i)]
variable (I : ∀ i, Ideal (R i)) (N : ∀ i, Submodule (R i) (M i)) (F : Filter ι)

open Filter

def eventuallyProd (F : Filter ι) : Submodule (Π i, R i) (Π i, M i) where
  carrier := { v | ∀ᶠ i in F, v i ∈ N i }
  add_mem' hv hw := by filter_upwards [hv, hw]; simp_all [add_mem]
  zero_mem' := by simp [zero_mem]
  smul_mem' r v hv := by filter_upwards [hv]; simp_all [Submodule.smul_mem]

variable {I} in
@[simp]
lemma mem_eventuallyProd {F : Filter ι} {x} :
    x ∈ eventuallyProd N F ↔ ∀ᶠ i in F, x i ∈ N i :=
  Iff.rfl

lemma eventuallyProd_mono_left
    {N₁ N₂ : Π i, Submodule (R i) (M i)} (h : N₁ ≤ N₂) :
    eventuallyProd N₁ F ≤ eventuallyProd N₂ F := by
  simp_rw [Pi.le_def, SetLike.le_def] at h
  exact fun x hx ↦ Eventually.mp hx (by aesop)

lemma eventuallyProd_mono_right {F G : Filter ι} (e : F ≤ G) :
    eventuallyProd N G ≤ eventuallyProd N F :=
  fun _ ↦ Eventually.filter_mono e

lemma eventuallyProd_eq_sup :
    eventuallyProd N F = eventuallyProd ⊥ F ⊔ Submodule.pi' N := by
  classical
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro x hx
    simp only [mem_eventuallyProd] at hx
    suffices ∃ y : Π i, M i, (∀ᶠ i in F, y i = 0) ∧ ∀ i, x i - y i ∈ N i by
      simpa [Submodule.mem_sup, @and_comm _ (_ = _), ← eq_sub_iff_add_eq']
    refine ⟨(fun i ↦ if x i ∈ N i then 0 else x i), ?_, fun i ↦ ?_⟩
    · filter_upwards [hx] with i hi
      exact if_pos hi
    · dsimp only
      split_ifs <;> simp[*]
  · exact fun x hx ↦ Eventually.mp hx (by aesop)
  · intro; simp_all

instance eventuallyProd.isPrime (F : Ultrafilter ι) [H : ∀ i, (I i).IsPrime] :
    Ideal.IsPrime (eventuallyProd I F) where
  ne_top' := by
    rw [ne_eq, Ideal.eq_top_iff_one]
    simp only [mem_eventuallyProd, Pi.one_apply, not_eventually]
    simp only [← Ideal.eq_top_iff_one, (H _).ne_top, not_false_eq_true,
      Ultrafilter.frequently_iff_eventually, eventually_true]
  mem_or_mem' := by
    intros v w
    simp only [mem_eventuallyProd, Pi.mul_apply, (H _).mul_mem_iff_mem_or_mem,
      Ultrafilter.eventually_or, imp_self]

variable (M) in
def UltraProduct : Type _ :=
  (Π i, M i) ⧸ eventuallyProd (R := fun _ ↦ ℤ) (M := M) ⊥ F

variable {F}

instance : AddCommGroup (UltraProduct M F) := inferInstanceAs
  (AddCommGroup ((Π i, M i) ⧸ eventuallyProd (R := fun _ ↦ ℤ) (M := M) ⊥ F))

instance : CommRing (UltraProduct R F) := inferInstanceAs
  (CommRing ((Π i, R i) ⧸ eventuallyProd (R := R) (M := R) ⊥ F))

variable (R F) in
def UltraProduct.π : (Π i, R i) →+* UltraProduct R F :=
  Ideal.Quotient.mk (eventuallyProd (R := R) (M := R) ⊥ F)

instance : Module (Π i, R i) (UltraProduct M F) :=
  inferInstanceAs (Module (Π i, R i) ((Π i, M i) ⧸ eventuallyProd (R := R) (M := M) ⊥ F))

variable (R M F) in
def UltraProduct.πₗ : (Π i, M i) →ₗ[Π i, R i] UltraProduct M F :=
  Submodule.mkQ (eventuallyProd (R := R) (M := M) ⊥ F)

lemma UltraProduct.π_surjective : Function.Surjective (π R F) :=
  Submodule.mkQ_surjective _

variable (R) in
lemma UltraProduct.πₗ_surjective : Function.Surjective (πₗ R M F) :=
  Submodule.mkQ_surjective _

variable {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra (R i) (A i)]

instance : Algebra (Π i, R i) (UltraProduct A F) where
  __ := (inferInstance : (Module (Π i, R i) (UltraProduct A F)))
  algebraMap := (UltraProduct.π A F).comp (algebraMap _ _)
  commutes' r x := Commute.all _ _
  smul_def' r x := by
    obtain ⟨x, rfl⟩ := UltraProduct.πₗ_surjective R x
    rw [← map_smul, Algebra.smul_def]
    change UltraProduct.π A F _ = _
    simp only [map_mul, RingHom.coe_comp, Function.comp_apply]
    rfl

variable {R₀} [∀ i, Module R₀ (M i)] [∀ i, IsScalarTower R₀ (R i) (M i)]
variable {M₀} [AddCommGroup M₀] [Module R₀ M₀]

instance : Module R₀ (UltraProduct M F) :=
  inferInstanceAs (Module R₀ ((Π i, M i) ⧸ eventuallyProd (R := fun _ ↦ R₀) (M := M) ⊥ F))

-- making this an instance timesout everything.
lemma UltraProduct.instIsScalarTower
    {R₁ : Type*} [CommRing R₁] [∀ i, Module R₁ (M i)] [Algebra R₀ R₁]
    [∀ i, IsScalarTower R₀ R₁ (M i)] :
    IsScalarTower R₀ R₁ (UltraProduct M F) :=
  inferInstanceAs (IsScalarTower R₀ R₁ ((Π i, M i) ⧸ eventuallyProd (R := fun _ ↦ R₁) (M := M) ⊥ F))

instance : Algebra R₀ (UltraProduct R F) :=
  inferInstanceAs (Algebra R₀ ((Π i, R i) ⧸ eventuallyProd (R := R) (M := R) ⊥ F))

set_option backward.isDefEq.respectTransparency false in
instance : IsScalarTower R₀ (Π i, R i) (UltraProduct M F) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  obtain ⟨m, rfl⟩ := UltraProduct.πₗ_surjective R m
  change _ = _ • Submodule.mkQ (eventuallyProd (R := fun _ ↦ R₀) (M := M) ⊥ F) m
  rw [← map_smul, ← LinearMap.map_smul_of_tower, algebraMap_smul]
  rfl

@[simp]
lemma UltraProduct.πₗ_eq_zero {x} : πₗ R M F x = 0 ↔ ∀ᶠ i in F, x i = 0 :=
  Submodule.Quotient.mk_eq_zero _

@[simp]
lemma UltraProduct.πₗ_eq_iff {x y} : πₗ R M F x = πₗ R M F y ↔ ∀ᶠ i in F, x i = y i :=
  (Submodule.Quotient.eq _).trans (by simp [sub_eq_zero])

@[simp]
lemma UltraProduct.π_eq_iff {x y} : π R F x = π R F y ↔ ∀ᶠ i in F, x i = y i :=
  (Submodule.Quotient.eq _).trans (by simp [sub_eq_zero])

@[simp]
lemma UltraProduct.π_eq_zero_iff {x} : π R F x = 0 ↔ ∀ᶠ i in F, x i = 0 :=
  UltraProduct.π_eq_iff

instance : SMul (UltraProduct R F) (UltraProduct M F) where
  smul := Quotient.lift₂ (UltraProduct.πₗ R M F <| · • ·) fun r₁ m₁ r₂ m₂ e₁ e₂ ↦ by
    rw [← sub_eq_zero]
    simp only [← map_sub, UltraProduct.πₗ_eq_zero]
    filter_upwards [(Submodule.quotientRel_def _).mp e₁,
      (Submodule.quotientRel_def _).mp e₂] with i h₁ h₂
    simp_all [sub_eq_zero]

@[simp]
lemma UltraProduct.π_smul {r} {m : UltraProduct M F} : π R F r • m = r • m := rfl

instance : Module (UltraProduct R F) (UltraProduct M F) :=
    Function.Surjective.moduleLeft (Ideal.Quotient.mk (eventuallyProd (R := R) (M := R) ⊥ F))
    UltraProduct.π_surjective fun _ _ ↦ UltraProduct.π_smul

set_option backward.isDefEq.respectTransparency false in
instance : IsScalarTower (Π i, R i) (UltraProduct R F) (UltraProduct M F) := by
  constructor
  intros r s m
  obtain ⟨s, rfl⟩ := UltraProduct.π_surjective s
  rw [UltraProduct.π_smul, ← UltraProduct.π_smul, smul_eq_mul, mul_smul,
    UltraProduct.π_smul, UltraProduct.π_smul]

set_option backward.isDefEq.respectTransparency false in
instance : IsScalarTower R₀ (UltraProduct R F) (UltraProduct M F) := by
  constructor
  intros r s m
  obtain ⟨s, rfl⟩ := UltraProduct.π_surjective s
  rw [UltraProduct.π_smul, ← @IsScalarTower.algebraMap_smul R₀ (Π i, R i),
    ← UltraProduct.π_smul, smul_eq_mul, mul_smul, UltraProduct.π_smul,
    UltraProduct.π_smul, IsScalarTower.algebraMap_smul]

instance : TopologicalSpace (UltraProduct M F) := ⊥
instance : DiscreteTopology (UltraProduct M F) := ⟨rfl⟩
instance : IsTopologicalAddGroup (UltraProduct M F) where
instance : IsTopologicalRing (UltraProduct R F) where

variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module (R i) (N i)]

variable (F) in
def UltraProduct.map (f : ∀ i, M i →ₗ[R i] N i) :
    UltraProduct M F →ₗ[∀ i, R i] UltraProduct N F :=
  Submodule.mapQ (eventuallyProd (R := R) (M := M) ⊥ F)
    (eventuallyProd (R := R) (M := N) ⊥ F) (LinearMap.piMap' f) fun v i ↦ by
    filter_upwards [i] with i hi; simpa using congr(f i $hi)

@[simp]
lemma UltraProduct.map_πₗ (f : ∀ i, M i →ₗ[R i] N i) (x) :
    UltraProduct.map F f (πₗ R M F x) = πₗ R N F (fun i ↦ f i (x i)) := rfl

variable (F) in
def UltraProduct.mapRingHom {S : ι → Type*} [∀ i, CommRing (S i)] (f : ∀ i, R i →+* S i) :
    UltraProduct R F →+* UltraProduct S F :=
  Ideal.quotientMap (I := eventuallyProd (R := R) (M := R) ⊥ F)
    (eventuallyProd (R := S) (M := S) ⊥ F) (Pi.ringHom fun i ↦ (f i).comp (Pi.evalRingHom _ i))
    (fun i H ↦ H.mono fun a ha ↦ by simp [show i a = 0 from ha])

@[simp]
lemma UltraProduct.mapRingHom_π {S : ι → Type*} [∀ i, CommRing (S i)] (f : ∀ i, R i →+* S i) (x) :
    mapRingHom F f (π R F x) = π S F (fun i ↦ f i (x i)) := rfl

variable (F) in
lemma UltraProduct.map_surjective (f : ∀ i, M i →ₗ[R i] N i)
    (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (map F f) := by
  intro x
  obtain ⟨x, rfl⟩ := πₗ_surjective R x
  choose y hy using fun i ↦ (hf _ (x i))
  exact ⟨πₗ R M F y, by simp [hy]⟩

variable (F) in
lemma UltraProduct.mapRingHom_surjective
    {S : ι → Type*} [∀ i, CommRing (S i)] (f : ∀ i, R i →+* S i)
    (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (mapRingHom F f) :=
  UltraProduct.map_surjective F (fun i ↦ (f i).toAddMonoidHom.toIntLinearMap) hf

variable {M₀ : Type*} [AddCommGroup M₀] [Module R₀ M₀] (f : ∀ i, M₀ →ₗ[R₀] M i)

lemma UltraProduct.surjective_of_eventually_surjective
    [Finite M₀] (F : Ultrafilter ι) (hf : ∀ᶠ i in F, Function.Surjective (f i)) :
    Function.Surjective ((πₗ (fun _ ↦ R₀) M F).restrictScalars R₀ ∘ₗ LinearMap.pi f) := by
  intro x
  obtain ⟨x, rfl⟩ := πₗ_surjective (fun _ ↦ R₀) x
  have : ∀ᶠ i in F, ∃ a, f i a = x i := by filter_upwards [hf] with i hi; exact hi _
  obtain ⟨a, ha⟩ := Ultrafilter.eventually_exists_iff.mp this
  exact ⟨a, UltraProduct.πₗ_eq_iff.mpr ha⟩

lemma UltraProduct.bijective_of_eventually_bijective
    [Finite M₀] (F : Ultrafilter ι) (hf : ∀ᶠ i in F, Function.Bijective (f i)) :
    Function.Bijective ((πₗ (fun _ ↦ R₀) M F).restrictScalars R₀ ∘ₗ LinearMap.pi f) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    replace hx : ∀ᶠ i in F, f i x = 0 := by simpa using hx
    obtain ⟨i, h₁, h₂⟩ := (hx.and hf).exists
    exact h₂.1 (h₁.trans (f i).map_zero.symm)
  · intro x
    obtain ⟨x, rfl⟩ := πₗ_surjective (fun _ ↦ R₀) x
    have : ∀ᶠ i in F, ∃ a, f i a = x i := by filter_upwards [hf] with i hi; exact hi.2 _
    obtain ⟨a, ha⟩ := Ultrafilter.eventually_exists_iff.mp this
    exact ⟨a, UltraProduct.πₗ_eq_iff.mpr ha⟩

lemma UltraProduct.isUnit_π_iff {x : Π i, R i} : IsUnit (π R F x) ↔ ∀ᶠ i in F, IsUnit (x i) := by
  simp_rw [isUnit_iff_exists_inv, π_surjective.exists, ← map_one (π R F), ← map_mul,
    UltraProduct.π_eq_iff]
  exact .symm <| Filter.skolem (P := (x · * · = 1))

instance {S : ι → Type*} [∀ i, CommRing (S i)] (f : ∀ i, R i →+* S i) [∀ i, IsLocalHom (f i)] :
    IsLocalHom (UltraProduct.mapRingHom F f) := by
  constructor
  intro a ha
  obtain ⟨a, rfl⟩ := UltraProduct.π_surjective a
  simp only [UltraProduct.mapRingHom_π, UltraProduct.isUnit_π_iff] at ha ⊢
  filter_upwards [ha] with i hi
  exact isUnit_of_map_unit _ _ hi

open scoped Classical in
lemma UltraProduct.exists_bijective_of_bddAbove_card [Algebra.FiniteType ℤ R₀]
    (F : Ultrafilter ι) (N : ℕ) (H : ∀ᶠ i in F, Finite (M i) ∧ Nat.card (M i) < N) :
    ∀ᶠ i in F,
      (∀ᶠ j in F, Nonempty (M i ≃ₗ[R₀] M j)) ∧
      Function.Bijective ((πₗ (fun _ ↦ R₀) M F).restrictScalars R₀ ∘ₗ LinearMap.pi fun j ↦
      if h : Nonempty (M i ≃ₗ[R₀] M j) then h.some.toLinearMap else 0) := by
  have : ∀ᶠ i in F, ∃ (α : ModuleTypeCardLT R₀ N), Nonempty (M i ≃ₗ[R₀] Fin α.1) := by
    filter_upwards [H] with i ⟨h₁, h₂⟩
    exact ⟨_, ⟨ModuleTypeCardLT.equivOfModule N h₂⟩⟩
  obtain ⟨a, ha⟩ := Ultrafilter.eventually_exists_iff.mp this
  filter_upwards [ha] with i ⟨ei⟩
  have := ei.toEquiv.finite_iff.mpr inferInstance
  refine ⟨?_, bijective_of_eventually_bijective _ _ ?_⟩
  · filter_upwards [ha] with j ⟨e⟩
    exact ⟨ei.trans e.symm⟩
  · filter_upwards [ha] with j ⟨e⟩
    rw [dif_pos ⟨ei.trans e.symm⟩]
    exact LinearEquiv.bijective _

/--
Let `R₀` be a topological ring, topologically of finite type (over `ℤ`).
Consider a family of (cardinality) finite continuous `R₀`-algebras `R i` with the discrete topology
whose cardinalites are unifomly bounded.

Then `𝒰(Rᵢ) ≃ₐ[R] R i` for `F`-many `i`.
-/
lemma UltraProduct.exists_algEquiv_of_bddAbove_card
    [TopologicalSpace R₀]
    [IsTopologicalRing R₀]
    [Algebra.TopologicallyFG ℤ R₀]
    [∀ i, TopologicalSpace (R i)]
    [∀ i, T2Space (R i)] (F : Ultrafilter ι)
    (N : ℕ) (H : ∀ᶠ i in F, Finite (R i) ∧ Nat.card (R i) < N)
    (hcont : ∀ᶠ i in F, ContinuousSMul R₀ (R i)) :
    ∀ᶠ i in F, Nonempty (UltraProduct R F ≃ₐ[R₀] R i) := by
  classical
  have : ∀ᶠ i in F, ∃ (α : TopologicalAlgebraTypeCardLT R₀ N)
    (e : R i ≃ₐ[R₀] Fin α.1), IsHomeomorph e := by
    filter_upwards [H, hcont] with i ⟨h₁, h₂⟩ h₃
    exact ⟨_, TopologicalAlgebraTypeCardLT.equivOfAlgebra N _ h₂,
      TopologicalAlgebraTypeCardLT.isHomeomorph_equivOfAlgebra N _ h₂⟩
  obtain ⟨a, ha⟩ := Ultrafilter.eventually_exists_iff.mp this
  let g (i) := if h : Nonempty (R i ≃ₐ[R₀] Fin a.1) then h.some.symm.toLinearMap else 0
  let e := LinearEquiv.ofBijective _
    (UltraProduct.bijective_of_eventually_bijective (R₀ := R₀) (M := R) (M₀ := Fin a.1) g F
    (by filter_upwards [ha] with i hi; unfold g;
        rw [dif_pos ⟨hi.choose⟩]; exact AlgEquiv.bijective _))
  let e' : Fin ↑a.fst ≃ₐ[R₀] UltraProduct R F := by
    refine AlgEquiv.ofLinearEquiv e ?_ ?_
    · rw [← (π R F).map_one]
      refine UltraProduct.πₗ_eq_iff.mpr ?_
      filter_upwards [ha] with i hi
      simp only [g, LinearMap.pi_apply, Pi.one_apply, dif_pos (Nonempty.intro (hi.choose)),
        AlgEquiv.toLinearMap_apply, map_one]
    · intro x y
      change _ = π R F _ * π R F _
      rw [← map_mul]
      refine UltraProduct.πₗ_eq_iff.mpr ?_
      filter_upwards [ha] with i hi
      simp only [LinearMap.pi_apply, dif_pos (Nonempty.intro (hi.choose)),
        AlgEquiv.toLinearMap_apply, map_mul, Pi.mul_apply, g]
  filter_upwards [ha] with i ⟨e, he⟩
  exact ⟨e'.symm.trans e.symm⟩

omit [∀ i, Algebra R₀ (R i)] in
/--
Let `R₀` be a topological ring, topologically of finite type (over `ℤ`).
Consider a family of (cardinality) finite rings `R i` with the discrete topology
whose cardinalites are unifomly bounded.

Given a family of continuous ring homs `f i : R →+* R i`, there exists `F`-many `i` such that
`𝒰(Rᵢ) ≃+* R i` and this map is compatible with `f`.
-/
lemma UltraProduct.exists_ringEquiv_of_bddAbove_card
    [TopologicalSpace R₀]
    [IsTopologicalRing R₀]
    [Algebra.TopologicallyFG ℤ R₀]
    [∀ i, TopologicalSpace (R i)]
    [∀ i, IsTopologicalRing (R i)]
    [∀ i, T2Space (R i)] (F : Ultrafilter ι)
    (N : ℕ) (H : ∀ᶠ i in F, Finite (R i) ∧ Nat.card (R i) < N)
    (f : ∀ i, R₀ →+* R i) (hf : ∀ᶠ i in F, Continuous (f i)) :
    ∀ᶠ i in F, ∃ e : UltraProduct R F ≃+*
      R i, e.toRingHom.comp ((π R F).comp (Pi.ringHom f)) = f i := by
  classical
  letI := fun i ↦ (f i).toAlgebra
  have := UltraProduct.exists_algEquiv_of_bddAbove_card (R₀ := R₀) F N H
    (by filter_upwards [hf] with i hi;
        exact ⟨show Continuous fun p : R₀ × R i ↦ f i p.1 * p.2 by continuity⟩)
  filter_upwards [this] with i ⟨e⟩
  exact ⟨e, e.toAlgHom.comp_algebraMap⟩

omit [∀ i, Algebra R₀ (R i)] in
/--
Let `R₀` be a topological ring, topologically of finite type (over `ℤ`).
Consider a family of (cardinality) finite rings `R i` with the discrete topology
whose cardinalites are unifomly bounded.

Given a family of continuous ring homs `f i : R →+* R i`, the lift `R →+* 𝒰(Rᵢ)` is also continuous.
-/
lemma UltraProduct.continuous_of_bddAbove_card
    [TopologicalSpace R₀]
    [IsTopologicalRing R₀]
    [Algebra.TopologicallyFG ℤ R₀]
    [∀ i, TopologicalSpace (R i)]
    [∀ i, IsTopologicalRing (R i)]
    [∀ i, T2Space (R i)] (F : Ultrafilter ι)
    (N : ℕ) (H : ∀ᶠ i in F, Finite (R i) ∧ Nat.card (R i) < N)
    (f : ∀ i, R₀ →+* R i) (hf : ∀ᶠ i in F, Continuous (f i)) :
    Continuous ((π R F).comp (Pi.ringHom f)) := by
  suffices IsOpen (X := R₀) (RingHom.ker ((π R F).comp (Pi.ringHom f))) by
    apply continuous_of_continuousAt_zero
    rw [ContinuousAt, map_zero, nhds_discrete (UltraProduct R F), pure_zero, tendsto_zero]
    exact this.mem_nhds (x := 0) (map_zero _)
  obtain ⟨i, ⟨e, he⟩, hf, hR, H⟩ :=
    ((UltraProduct.exists_ringEquiv_of_bddAbove_card F N H f hf).and (hf.and H)).exists
  have : e.symm.toRingHom.comp (f i) = (π R F).comp (Pi.ringHom f) := by
    rw [← he, ← RingHom.comp_assoc]; simp
  rw [← this, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot e.symm.toRingHom).mp e.symm.injective]
  exact hf.isOpen_preimage {0} (isOpen_discrete {0})

omit [∀ i, Algebra R₀ (R i)] in
/--
Let `R₀` be a topological ring, topologically of finite type (over `ℤ`).
Consider a family of (cardinality) finite rings `R i` with the discrete topology
whose cardinalites are unifomly bounded.

Given a family of continuous surjective ring homs `f i : R →+* R i`,
the lift `R →+* 𝒰(Rᵢ)` is also surjective.
-/
lemma UltraProduct.surjective_of_bddAbove_card
    [TopologicalSpace R₀]
    [IsTopologicalRing R₀]
    [Algebra.TopologicallyFG ℤ R₀]
    [∀ i, TopologicalSpace (R i)]
    [∀ i, IsTopologicalRing (R i)]
    [∀ i, T2Space (R i)] (F : Ultrafilter ι)
    (N : ℕ) (H : ∀ᶠ i in F, Finite (R i) ∧ Nat.card (R i) < N)
    (f : ∀ i, R₀ →+* R i) (hf : ∀ᶠ i in F, Continuous (f i))
    (hf' : ∀ᶠ i in F, Function.Surjective (f i)) :
    Function.Surjective ((π R F).comp (Pi.ringHom f)) := by
  obtain ⟨i, ⟨e, he⟩, hf⟩ :=
    ((UltraProduct.exists_ringEquiv_of_bddAbove_card F N H f hf).and hf').exists
  have : e.symm.toRingHom.comp (f i) = (π R F).comp (Pi.ringHom f) := by
    rw [← he, ← RingHom.comp_assoc]; simp
  rw [← this]
  exact e.symm.surjective.comp hf
