import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Data.Complex.Basic

open Complex Metric

noncomputable section

open scoped Real BigOperators

/-- The closed unit disk is the points within distance `1` of the origin. -/
def closedUnitDisk : Set ℂ := Metric.closedBall 0 1

/-- The unit circle is the sphere of radius `1` centered at the origin. -/
def unitCircle : Set ℂ := Metric.sphere 0 1

/-- The zeros of `f` inside the closed unit disk. -/
def zeroSet (f : ℂ → ℂ) : Set ℂ :=
  {z : ℂ | z ∈ closedUnitDisk ∧ f z = 0}

/-- The zeros of the derivative inside the closed disk. -/
def derivZeroSet (f : ℂ → ℂ) : Set ℂ :=
  zeroSet (deriv f)

/-- The finite-cardinality zero count, once finiteness is known. -/
noncomputable def zeroCount (f : ℂ → ℂ)
    (hfin : (zeroSet f).Finite) : ℕ :=
  (hfin.toFinset.card)

noncomputable def zeroFinset (f : ℂ → ℂ)
    (hfin : (zeroSet f).Finite) : Finset ℂ :=
  hfin.toFinset

@[simp] lemma mem_zeroFinset {f : ℂ → ℂ}
    {hfin : (zeroSet f).Finite} {z : ℂ} :
    z ∈ zeroFinset f hfin ↔ z ∈ zeroSet f := by
  classical
  simp [zeroFinset]

@[simp] lemma zeroCount_eq_card (f : ℂ → ℂ)
    (hfin : (zeroSet f).Finite) :
    zeroCount f hfin = hfin.toFinset.card := rfl

@[simp] lemma card_zeroFinset (f : ℂ → ℂ)
    (hfin : (zeroSet f).Finite) :
    (zeroFinset f hfin).card = zeroCount f hfin := by
  classical
  simp [zeroFinset, zeroCount_eq_card]

@[simp] lemma zeroCount_eq_zero (f : ℂ → ℂ)
    (hfin : (zeroSet f).Finite) :
    zeroCount f hfin = 0 ↔ zeroFinset f hfin = ∅ := by
  classical
  simpa [card_zeroFinset] using
    (Finset.card_eq_zero :
      (zeroFinset f hfin).card = 0 ↔ zeroFinset f hfin = ∅)

@[simp] lemma zeroCount_pos (f : ℂ → ℂ)
    (hfin : (zeroSet f).Finite) :
    0 < zeroCount f hfin ↔ (zeroFinset f hfin).Nonempty := by
  classical
  have := (Finset.card_pos :
    0 < (zeroFinset f hfin).card ↔ (zeroFinset f hfin).Nonempty)
  simpa [card_zeroFinset] using this

/-- Zero count for the derivative, using `derivZeroSet`. -/
noncomputable def derivZeroCount (f : ℂ → ℂ)
    (hfin : (derivZeroSet f).Finite) : ℕ :=
  zeroCount (deriv f) (by simpa [derivZeroSet] using hfin)

noncomputable def derivZeroFinset (f : ℂ → ℂ)
    (hfin : (derivZeroSet f).Finite) : Finset ℂ :=
  (by simpa [derivZeroSet] using hfin :
      (zeroSet (deriv f)).Finite).toFinset

@[simp] lemma mem_derivZeroFinset {f : ℂ → ℂ}
    {hfin : (derivZeroSet f).Finite} {z : ℂ} :
    z ∈ derivZeroFinset f hfin ↔ z ∈ derivZeroSet f := by
  classical
  simp [derivZeroFinset, derivZeroSet]

@[simp] lemma derivZeroCount_eq_card (f : ℂ → ℂ)
    (hfin : (derivZeroSet f).Finite) :
    derivZeroCount f hfin =
      ((by simpa [derivZeroSet] using hfin :
        (zeroSet (deriv f)).Finite).toFinset.card) := by
  unfold derivZeroCount
  classical
  simp [zeroCount_eq_card]

@[simp] lemma card_derivZeroFinset (f : ℂ → ℂ)
    (hfin : (derivZeroSet f).Finite) :
    (derivZeroFinset f hfin).card = derivZeroCount f hfin := by
  classical
  simp [derivZeroFinset, derivZeroCount, zeroCount_eq_card]

@[simp] lemma derivZeroCount_eq_zero (f : ℂ → ℂ)
    (hfin : (derivZeroSet f).Finite) :
    derivZeroCount f hfin = 0 ↔ derivZeroFinset f hfin = ∅ := by
  classical
  simpa [card_derivZeroFinset] using
    (Finset.card_eq_zero :
      (derivZeroFinset f hfin).card = 0 ↔
        derivZeroFinset f hfin = ∅)

@[simp] lemma derivZeroCount_pos (f : ℂ → ℂ)
    (hfin : (derivZeroSet f).Finite) :
    0 < derivZeroCount f hfin ↔
      (derivZeroFinset f hfin).Nonempty := by
  classical
  have := (Finset.card_pos :
    0 < (derivZeroFinset f hfin).card ↔
      (derivZeroFinset f hfin).Nonempty)
  simpa [card_derivZeroFinset] using this


lemma mem_zeroSet {f : ℂ → ℂ} {z : ℂ} :
    z ∈ zeroSet f ↔ z ∈ closedUnitDisk ∧ f z = 0 := Iff.rfl

/-- Every zero of `f` in `zeroSet f` lies in the closed unit disk. -/
lemma zeroSet_subset_closedUnitDisk (f : ℂ → ℂ) :
    zeroSet f ⊆ closedUnitDisk := by
  intro z hz
  exact (mem_zeroSet.mp hz).1

lemma zeroFinset_subset_closedUnitDisk (f : ℂ → ℂ)
    (hfin : (zeroSet f).Finite) :
    (zeroFinset f hfin : Set ℂ) ⊆ closedUnitDisk := by
  intro z hz
  have hz' : z ∈ zeroSet f := by
    classical
    simpa [Finset.mem_coe] using (mem_zeroFinset.mp hz)
  exact zeroSet_subset_closedUnitDisk f hz'

lemma zeroSet_mul_const {f : ℂ → ℂ} {μ : ℂ} (hμ : μ ≠ 0) :
    zeroSet (fun z => μ * f z) = zeroSet f := by
  ext z
  constructor <;> intro hz
  · rcases hz with ⟨hz₁, hz₂⟩
    have hf : f z = 0 := by
      rcases (mul_eq_zero.mp hz₂) with hμ' | hf
      · exact (hμ hμ').elim
      · exact hf
    exact ⟨hz₁, hf⟩
  · rcases hz with ⟨hz₁, hz₂⟩
    exact ⟨hz₁, by simpa [hz₂]⟩

lemma derivZeroSet_mul_const {f : ℂ → ℂ} {μ : ℂ} (hμ : μ ≠ 0) :
    derivZeroSet (fun z => μ * f z) = derivZeroSet f := by
  have hderiv :=
    (deriv_const_mul_field' (u := μ) (v := f))
  simpa [derivZeroSet, hderiv] using
    (zeroSet_mul_const (f := deriv f) hμ)

lemma derivZeroSet_subset_closedUnitDisk (f : ℂ → ℂ) :
    derivZeroSet f ⊆ closedUnitDisk := by
  intro z hz
  have : z ∈ zeroSet (deriv f) := by simpa [derivZeroSet] using hz
  exact zeroSet_subset_closedUnitDisk (deriv f) this

lemma derivZeroFinset_subset_closedUnitDisk (f : ℂ → ℂ)
    (hfin : (derivZeroSet f).Finite) :
    (derivZeroFinset f hfin : Set ℂ) ⊆ closedUnitDisk := by
  intro z hz
  have hz' : z ∈ derivZeroSet f := by
    classical
    simpa [Finset.mem_coe] using (mem_derivZeroFinset.mp hz)
  exact derivZeroSet_subset_closedUnitDisk f hz'

lemma zeroSet_congr {f g : ℂ → ℂ}
    (hfg : ∀ ⦃z⦄, z ∈ closedUnitDisk → f z = g z) :
    zeroSet f = zeroSet g := by
  ext z
  constructor
  · intro hz
    refine And.intro hz.1 ?_
    simpa [hz.2] using (hfg hz.1).symm
  · intro hz
    refine And.intro hz.1 ?_
    simpa [hz.2] using hfg hz.1

lemma zeroSet_eq_empty_of_nonvanishing {f : ℂ → ℂ}
    (h : ∀ z ∈ closedUnitDisk, f z ≠ 0) :
    zeroSet f = ∅ := by
  ext z
  constructor
  · intro hz
    have := h z hz.1
    simpa [hz.2] using this
  · intro hz
    simpa using hz

lemma zeroCount_eq_zero_of_nonvanishing {f : ℂ → ℂ}
    (hfin : (zeroSet f).Finite)
    (h : ∀ z ∈ closedUnitDisk, f z ≠ 0) :
    zeroCount f hfin = 0 := by
  classical
  have hzero :
      zeroFinset f hfin = ∅ := by
    ext z
    simp [mem_zeroFinset, zeroSet_eq_empty_of_nonvanishing h]
  exact (zeroCount_eq_zero f hfin).mpr hzero

lemma zeroCount_congr {f g : ℂ → ℂ}
    (hfg : ∀ ⦃z⦄, z ∈ closedUnitDisk → f z = g z)
    (hfin : (zeroSet f).Finite) :
    zeroCount f hfin =
      zeroCount g
        (by simpa [zeroSet_congr hfg] using hfin) := by
  classical
  simp [zeroCount, zeroSet_congr hfg]

lemma zeroFinset_congr {f g : ℂ → ℂ}
    (hfg : ∀ ⦃z⦄, z ∈ closedUnitDisk → f z = g z)
    (hfin : (zeroSet f).Finite) :
    zeroFinset f hfin =
      zeroFinset g
        (by simpa [zeroSet_congr hfg] using hfin) := by
  classical
  ext z
  simp [zeroFinset, zeroSet_congr hfg]

 /-- An analytic function on the closed unit disk is continuous there. -/
lemma analyticOn_closedUnitDisk_continuous
    {f : ℂ → ℂ} (hhol : AnalyticOn ℂ f closedUnitDisk) :
    ContinuousOn f closedUnitDisk :=
  hhol.continuousOn

/-- On the boundary we have `‖f z‖ = 1`, so no boundary point can be a zero. -/
lemma boundary_has_no_zeros {f : ℂ → ℂ}
    (hbdry : ∀ z ∈ unitCircle, ‖f z‖ = 1) :
    ∀ z ∈ unitCircle, f z ≠ 0 := by
  intro z hz hz0
  have hnorm : ‖f z‖ = 1 := hbdry z hz
  have : ‖f z‖ = 0 := by simpa [hz0] using (norm_zero (f z))
  have : (1 : ℝ) = 0 := by simpa [hnorm] using this
  exact one_ne_zero this

/-- Every point on the unit circle lies in the closed unit disk. -/
lemma unitCircle_subset_closedUnitDisk :
    unitCircle ⊆ closedUnitDisk := by
  intro z hz
  have hz' : dist z 0 = 1 := by
    simpa [unitCircle, dist_comm] using hz
  have : dist z 0 ≤ 1 := hz'.le
  simpa [closedUnitDisk] using this

/-- Canonical factors have modulus one on the unit circle. -/
lemma canonicalFactor_unitCircle_norm_one
    {w z : ℂ} (hw : ‖w‖ < 1) (hz : z ∈ unitCircle) :
    ‖canonicalFactor (1 : ℝ) w z‖ = 1 := by
  have hw' : w ∈ Metric.ball (0 : ℂ) (1 : ℝ) := by
    simpa [Metric.ball, dist_eq, sub_zero] using hw
  have hz' : z ∈ Metric.sphere (0 : ℂ) (1 : ℝ) := by
    simpa [unitCircle, dist_comm] using hz
  simpa [unitCircle] using
    (Complex.norm_canonicalFactor_eval_circle_eq_one
      (R := (1 : ℝ)) (w := w) (z := z) hw' hz')

/-- A finite product of unit-modulus complex numbers again has modulus one. -/
lemma norm_finset_prod_eq_one {ι : Type*} :
    ∀ (s : Finset ι) (f : ι → ℂ),
      (∀ i ∈ s, ‖f i‖ = 1) →
        ‖∏ i ∈ s, f i‖ = 1 := by
  classical
  intro s
  refine Finset.induction_on s ?base ?step
  · intro f _
    simp
  · intro a s ha ih f hf
    have hnorm : ‖f a‖ = 1 := hf a (by simp [Finset.mem_insert])
    have hrest :
        ∀ i ∈ s, ‖f i‖ = 1 := by
      intro i hi
      have : i = a ∨ i ∈ s := Or.inr hi
      exact hf i (by simpa [Finset.mem_insert] using this)
    calc
      ‖∏ i ∈ insert a s, f i‖
          = ‖f a * ∏ i ∈ s, f i‖ := by
            simp [Finset.prod_insert, ha]
      _ = ‖f a‖ * ‖∏ i ∈ s, f i‖ := by
            simpa using norm_mul (f a) (∏ i ∈ s, f i)
      _ = 1 * 1 := by simp [hnorm, ih f hrest]
      _ = 1 := one_mul _

/-- The closed unit disk is compact. -/
lemma isCompact_closedUnitDisk : IsCompact closedUnitDisk := by
  simpa [closedUnitDisk] using (isCompact_closedBall (0 : ℂ) (1 : ℝ))

/-- The closed unit disk is a closed set. -/
lemma isClosed_closedUnitDisk : IsClosed closedUnitDisk := by
  simpa [closedUnitDisk] using
    (Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := (1 : ℝ)))

/-- The unit circle is compact. -/
lemma isCompact_unitCircle : IsCompact unitCircle := by
  simpa [unitCircle] using (isCompact_sphere (0 : ℂ) (1 : ℝ))

lemma isClosed_unitCircle : IsClosed unitCircle := by
  simpa [unitCircle] using
    (Metric.isClosed_sphere (x := (0 : ℂ)) (ε := (1 : ℝ)))

/-- A tiny sanity check: the canonical factor vanishes at its pole. -/
lemma canonicalFactor_self_zero (R : ℝ) (w : ℂ) :
    canonicalFactor R w w = 0 := by
  simpa using canonicalFactor_apply_self R w

/-- Zeros of an analytic function on the closed unit disk are finite. -/
lemma zeroSet_finite_of_analytic
    {f : ℂ → ℂ}
    (hhol : AnalyticOn ℂ f closedUnitDisk) :
    (zeroSet f).Finite := by
  classical
  -- TODO: use discreteness of zeros plus compactness of the closed disk.
  sorry

/-- Critical points inside the closed disk are finite as well. -/
lemma derivZeroSet_finite_of_analytic
    {f : ℂ → ℂ}
    (hhol : AnalyticOn ℂ f closedUnitDisk) :
    (derivZeroSet f).Finite := by
  classical
  -- TODO: apply the previous lemma to `deriv f`.
  sorry

/-- Blaschke product factoring: boundary modulus one forces the canonical product formula. -/
lemma blaschke_factorization
    (f : ℂ → ℂ)
    (hhol : AnalyticOn ℂ f closedUnitDisk)
    (hbdry : ∀ z ∈ unitCircle, ‖f z‖ = 1) :
    ∃ μ : ℂ, μ ≠ 0 ∧ ‖μ‖ = 1 ∧
      ∀ z ∈ closedUnitDisk,
        f z =
          μ * ∏ w ∈ zeroFinset f (zeroSet_finite_of_analytic hhol),
            canonicalFactor (1 : ℝ) w z := by
  classical
  -- TODO: invoke the standard finite Blaschke product decomposition.
  sorry

/-- Gauss–Lucas style control: derivative zeros lie inside the convex hull. -/
lemma derivative_zero_subset
    (f : ℂ → ℂ)
    (hhol : AnalyticOn ℂ f closedUnitDisk) :
    derivZeroSet f ⊆
      ConvexHull ℂ (zeroSet f) := by
  classical
  -- TODO: apply the Gauss–Lucas theorem tailored to the Blaschke product.
  sorry

/-- Main quantitative statement: `deriv f` has exactly one fewer zero. -/
theorem derivative_zero_count
    (f : ℂ → ℂ)
    (hhol : AnalyticOn ℂ f closedUnitDisk)
    (hbdry : ∀ z ∈ unitCircle, ‖f z‖ = 1)
    (N : ℕ)
    (hN : zeroCount f (zeroSet_finite_of_analytic hhol) = N.succ) :
    derivZeroCount f (derivZeroSet_finite_of_analytic hhol) = N := by
  classical
  -- Outline: factor `f` as a finite Blaschke product, differentiate the product,
  -- and count multiplicities using the Gauss–Lucas theorem inside the unit disk.
  sorry

/-- Final form of the APM problem statement. -/
theorem apm_a01J05_main
    (f : ℂ → ℂ)
    (hhol : AnalyticOn ℂ f closedUnitDisk)
    (hbdry : ∀ z ∈ unitCircle, ‖f z‖ = 1)
    (N : ℕ)
    (hN : zeroCount f (zeroSet_finite_of_analytic hhol) = N.succ) :
    ∃ zerosDeriv : ℕ,
      zerosDeriv = N ∧
        derivZeroCount f (derivZeroSet_finite_of_analytic hhol) = zerosDeriv := by
  refine ⟨N, rfl, ?_⟩
  simpa using
    (derivative_zero_count f hhol hbdry N hN)
