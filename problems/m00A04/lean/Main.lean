import Mathlib

/-!
# APM m00A04: Hilbert-space minimization and a weak elliptic solution

## Statement repairs

In part (a), the strict-minimum clause prints `V ≠ u`; since `V` is the
ambient space, this is ill-typed. We replace it by the intended `v ≠ u`.

## Encoding questions

This Mathlib snapshot has no packaged `H¹₀(Ω)` space. Rather than replacing it
by a scalar shadow, `apm_m00A04_memH10WithGradient` explicitly encodes its
standard definition: an `L²` function with `L²` distributional weak gradient
that is approximable in the energy norm by smooth compactly supported tests.
-/

open MeasureTheory Set Function
open scoped ContDiff BigOperators RealInnerProductSpace

noncomputable section

def apm_m00A04_phi {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V →L[ℝ] ℝ) (v : V) : ℝ :=
  (1 / 2 : ℝ) * ‖v‖ ^ 2 - f v

/-- Smooth compactly supported test functions on `U`.  Compact support is
encoded honestly by `HasCompactSupport`, i.e. compactness of the *closure* of
the support; requiring the raw support itself to be compact would force every
test function to vanish in positive dimension. -/
def apm_m00A04_testFunction {n : ℕ} (U : Set (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

def apm_m00A04_partial {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ φ x (Pi.single i 1)

def apm_m00A04_L2On {n : ℕ} (U : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ) : Prop :=
  AEStronglyMeasurable u (volume.restrict U) ∧
    IntegrableOn (fun x ↦ |u x| ^ 2) U

def apm_m00A04_weakGradient {n : ℕ} (U : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ)
    (g : Fin n → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin n) (φ : (Fin n → ℝ) → ℝ),
    apm_m00A04_testFunction U φ →
      (∫ x in U, u x * apm_m00A04_partial φ i x) =
        -∫ x in U, g i x * φ x

/-- An explicit representative-level encoding of `u ∈ H¹₀(U)` with weak
gradient `g`. -/
def apm_m00A04_memH10WithGradient {n : ℕ} (U : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ)
    (g : Fin n → (Fin n → ℝ) → ℝ) : Prop :=
  apm_m00A04_L2On U u ∧
  (∀ i, apm_m00A04_L2On U (g i)) ∧
  apm_m00A04_weakGradient U u g ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ φ : (Fin n → ℝ) → ℝ,
      apm_m00A04_testFunction U φ ∧
      (∫ x in U,
        |u x - φ x| ^ 2 +
          ∑ i : Fin n, |g i x - apm_m00A04_partial φ i x| ^ 2) < ε

/-! The following bundled pair and two pairings isolate the exact consumer
interface needed by the eventual completion argument.  In particular, this
keeps the construction of the Sobolev completion independent of the final
raw-function presentation. -/

structure apm_m00A04_EnergyPair (n : ℕ) where
  value : (Fin n → ℝ) → ℝ
  gradient : Fin n → (Fin n → ℝ) → ℝ

def apm_m00A04_energyDensity {n : ℕ}
    (p q : apm_m00A04_EnergyPair n) (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, p.gradient i x * q.gradient i x) + p.value x * q.value x

def apm_m00A04_energyPairing {n : ℕ} (U : Set (Fin n → ℝ))
    (p q : apm_m00A04_EnergyPair n) : ℝ :=
  ∫ x in U, apm_m00A04_energyDensity p q x

def apm_m00A04_forcingPairing {n : ℕ} (U : Set (Fin n → ℝ))
    (F : (Fin n → ℝ) → ℝ) (p : apm_m00A04_EnergyPair n) : ℝ :=
  ∫ x in U, F x * p.value x

lemma apm_m00A04_energyDensity_comm {n : ℕ}
    (p q : apm_m00A04_EnergyPair n) (x : Fin n → ℝ) :
    apm_m00A04_energyDensity p q x = apm_m00A04_energyDensity q p x := by
  simp only [apm_m00A04_energyDensity]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  · exact mul_comm _ _

lemma apm_m00A04_energyPairing_comm {n : ℕ} (U : Set (Fin n → ℝ))
    (p q : apm_m00A04_EnergyPair n) :
    apm_m00A04_energyPairing U p q = apm_m00A04_energyPairing U q p := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  exact apm_m00A04_energyDensity_comm p q x

lemma apm_m00A04_energyDensity_self_nonneg {n : ℕ}
    (p : apm_m00A04_EnergyPair n) (x : Fin n → ℝ) :
    0 ≤ apm_m00A04_energyDensity p p x := by
  simp only [apm_m00A04_energyDensity]
  exact add_nonneg
    (Finset.sum_nonneg fun i hi ↦ mul_self_nonneg (p.gradient i x))
    (mul_self_nonneg (p.value x))

lemma apm_m00A04_energyPairing_self_nonneg {n : ℕ}
    (U : Set (Fin n → ℝ)) (p : apm_m00A04_EnergyPair n) :
    0 ≤ apm_m00A04_energyPairing U p p := by
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [] with x
  exact apm_m00A04_energyDensity_self_nonneg p x

lemma apm_m00A04_variational_iff_pairing {n : ℕ} (U : Set (Fin n → ℝ))
    (F u : (Fin n → ℝ) → ℝ)
    (g : Fin n → (Fin n → ℝ) → ℝ) :
    (∀ (v : (Fin n → ℝ) → ℝ)
      (h : Fin n → (Fin n → ℝ) → ℝ),
      apm_m00A04_memH10WithGradient U v h →
        (∫ x in U, (∑ i : Fin n, g i x * h i x) + u x * v x) =
          ∫ x in U, F x * v x) ↔
    (∀ q : apm_m00A04_EnergyPair n,
      apm_m00A04_memH10WithGradient U q.value q.gradient →
        apm_m00A04_energyPairing U ⟨u, g⟩ q =
          apm_m00A04_forcingPairing U F q) := by
  constructor
  · intro H q hq
    exact H q.value q.gradient hq
  · intro H v h hv
    exact H ⟨v, h⟩ hv

lemma apm_m00A04_testFunction_neg {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ) :
    apm_m00A04_testFunction U (-φ) := by
  rcases hφ with ⟨hφdiff, hφcompact, hφsupport⟩
  have hts : tsupport (-φ) = tsupport φ := by
    rw [tsupport, tsupport, Function.support_neg]
  refine ⟨hφdiff.neg, ?_, ?_⟩
  · show IsCompact (tsupport (-φ))
    rwa [hts]
  · rwa [hts]

lemma apm_m00A04_partial_neg {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    apm_m00A04_partial (-φ) i x = -apm_m00A04_partial φ i x := by
  simp only [apm_m00A04_partial, fderiv_neg, ContinuousLinearMap.neg_apply]

lemma apm_m00A04_testFunction_smul {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} (c : ℝ) (hc : c ≠ 0)
    (hφ : apm_m00A04_testFunction U φ) :
    apm_m00A04_testFunction U (c • φ) := by
  rcases hφ with ⟨hφdiff, hφcompact, hφsupport⟩
  have hsupp : Function.support (c • φ) = Function.support φ := by
    ext x
    simp [Function.mem_support, hc]
  have hts : tsupport (c • φ) = tsupport φ := by
    rw [tsupport, tsupport, hsupp]
  refine ⟨hφdiff.const_smul c, ?_, ?_⟩
  · show IsCompact (tsupport (c • φ))
    rwa [hts]
  · rwa [hts]

lemma apm_m00A04_partial_smul {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (c : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    apm_m00A04_partial (c • φ) i x = c * apm_m00A04_partial φ i x := by
  unfold apm_m00A04_partial
  rw [fderiv_const_smul (hφ.differentiable (by simp)).differentiableAt c]
  simp

lemma apm_m00A04_memH10WithGradient_neg {n : ℕ} {U : Set (Fin n → ℝ)}
    {u : (Fin n → ℝ) → ℝ} {g : Fin n → (Fin n → ℝ) → ℝ}
    (hug : apm_m00A04_memH10WithGradient U u g) :
    apm_m00A04_memH10WithGradient U (-u) (-g) := by
  rcases hug with ⟨hu, hg, hw, happ⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨hu.1.neg, by simpa only [Pi.neg_apply, abs_neg] using hu.2⟩
  · intro i
    exact ⟨(hg i).1.neg, by simpa only [Pi.neg_apply, abs_neg] using (hg i).2⟩
  · intro i φ hφ
    have hi := hw i φ hφ
    simp only [Pi.neg_apply, neg_mul]
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg, hi]
  · intro ε hε
    obtain ⟨φ, hφ, happrox⟩ := happ ε hε
    refine ⟨-φ, apm_m00A04_testFunction_neg hφ, ?_⟩
    simpa only [Pi.neg_apply, apm_m00A04_partial_neg, neg_sub_neg, abs_neg,
      abs_sub_comm] using happrox

private lemma apm_m00A04_zero_memH10WithGradient {n : ℕ}
    (U : Set (Fin n → ℝ)) :
    apm_m00A04_memH10WithGradient U 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨aestronglyMeasurable_zero, by simp⟩
  · intro i
    exact ⟨aestronglyMeasurable_zero, by simp⟩
  · intro i φ hφ
    simp
  · intro ε hε
    refine ⟨0, ?_, ?_⟩
    · refine ⟨contDiff_const, ?_, ?_⟩
      · have hts : tsupport (0 : (Fin n → ℝ) → ℝ) = ∅ := by
          simp [tsupport, Function.support]
        show IsCompact (tsupport (0 : (Fin n → ℝ) → ℝ))
        rw [hts]
        exact isCompact_empty
      · show tsupport (0 : (Fin n → ℝ) → ℝ) ⊆ U
        simp [tsupport, Function.support]
    · simpa [apm_m00A04_partial] using hε

lemma apm_m00A04_memH10WithGradient_smul {n : ℕ} {U : Set (Fin n → ℝ)}
    {u : (Fin n → ℝ) → ℝ} {g : Fin n → (Fin n → ℝ) → ℝ}
    (hug : apm_m00A04_memH10WithGradient U u g) (c : ℝ) :
    apm_m00A04_memH10WithGradient U (c • u) (c • g) := by
  by_cases hc : c = 0
  · subst c
    simpa using apm_m00A04_zero_memH10WithGradient U
  rcases hug with ⟨hu, hg, hw, happ⟩
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hu.1.const_smul c, ?_⟩
    have hi := hu.2.const_mul (|c| ^ 2)
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_pow] using hi
  · intro i
    refine ⟨(hg i).1.const_smul c, ?_⟩
    have hi := (hg i).2.const_mul (|c| ^ 2)
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, mul_pow] using hi
  · intro i φ hφ
    have hi := hw i φ hφ
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [MeasureTheory.integral_const_mul, hi]
    calc
      c * -∫ x in U, g i x * φ x =
          -(c * ∫ x in U, g i x * φ x) := by ring
      _ = -∫ x in U, c * (g i x * φ x) := by
        rw [MeasureTheory.integral_const_mul]
  · intro ε hε
    obtain ⟨φ, hφ, happrox⟩ := happ (ε / c ^ 2) (div_pos hε hc2)
    refine ⟨c • φ, apm_m00A04_testFunction_smul c hc hφ, ?_⟩
    have hscale :
        (∫ x in U,
          |(c • u) x - (c • φ) x| ^ 2 +
            ∑ i : Fin n,
              |(c • g) i x - apm_m00A04_partial (c • φ) i x| ^ 2) =
          c ^ 2 *
            ∫ x in U,
              |u x - φ x| ^ 2 +
                ∑ i : Fin n, |g i x - apm_m00A04_partial φ i x| ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simp only [Pi.smul_apply, smul_eq_mul,
        apm_m00A04_partial_smul φ hφ.1 c]
      rw [← sq_abs c]
      simp_rw [← mul_sub, abs_mul, mul_pow]
      rw [← Finset.mul_sum]
      ring
    rw [hscale]
    calc
      c ^ 2 * (∫ x in U,
          |u x - φ x| ^ 2 +
            ∑ i : Fin n, |g i x - apm_m00A04_partial φ i x| ^ 2) <
          c ^ 2 * (ε / c ^ 2) := mul_lt_mul_of_pos_left happrox hc2
      _ = ε := by field_simp

private lemma apm_m00A04_zero_weak_solution {n : ℕ}
    (U : Set (Fin n → ℝ)) :
    ∃ (u : (Fin n → ℝ) → ℝ)
      (g : Fin n → (Fin n → ℝ) → ℝ),
      apm_m00A04_memH10WithGradient U u g ∧
      ∀ (v : (Fin n → ℝ) → ℝ)
        (h : Fin n → (Fin n → ℝ) → ℝ),
        apm_m00A04_memH10WithGradient U v h →
          (∫ x in U, (∑ i : Fin n, g i x * h i x) + u x * v x) =
            ∫ x in U, (0 : ℝ) * v x := by
  refine ⟨0, 0, apm_m00A04_zero_memH10WithGradient U, ?_⟩
  intro v h hv
  simp


lemma apm_m00A04_testFunction_add {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ ψ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ)
    (hψ : apm_m00A04_testFunction U ψ) :
    apm_m00A04_testFunction U (φ + ψ) := by
  rcases hφ with ⟨hφdiff, hφcompact, hφsupport⟩
  rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
  have hsub : Function.support (φ + ψ) ⊆ tsupport φ ∪ tsupport ψ := by
    intro x hx
    by_contra hxnot
    simp only [Set.mem_union, not_or] at hxnot
    have h1 : φ x = 0 := Function.notMem_support.mp
      (fun h ↦ hxnot.1 (subset_tsupport _ h))
    have h2 : ψ x = 0 := Function.notMem_support.mp
      (fun h ↦ hxnot.2 (subset_tsupport _ h))
    rw [Function.mem_support] at hx
    exact hx (by simp [Pi.add_apply, h1, h2])
  have hts : tsupport (φ + ψ) ⊆ tsupport φ ∪ tsupport ψ :=
    closure_minimal hsub (isClosed_closure.union isClosed_closure)
  refine ⟨hφdiff.add hψdiff, ?_, ?_⟩
  · exact (hφcompact.union hψcompact).of_isClosed_subset isClosed_closure hts
  · exact hts.trans (Set.union_subset hφsupport hψsupport)

lemma apm_m00A04_partial_add {n : ℕ} {φ ψ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin n) (x : Fin n → ℝ) :
    apm_m00A04_partial (φ + ψ) i x =
      apm_m00A04_partial φ i x + apm_m00A04_partial ψ i x := by
  unfold apm_m00A04_partial
  rw [fderiv_add (hφ.differentiable (by simp)).differentiableAt
    (hψ.differentiable (by simp)).differentiableAt]
  rfl

lemma apm_m00A04_partial_zero {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    apm_m00A04_partial (0 : (Fin n → ℝ) → ℝ) i x = 0 := by
  simp [apm_m00A04_partial]

lemma apm_m00A04_partial_continuous {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (i : Fin n) :
    Continuous (apm_m00A04_partial φ i) := by
  unfold apm_m00A04_partial
  exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

lemma apm_m00A04_partial_hasCompactSupport {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : HasCompactSupport φ) (i : Fin n) :
    HasCompactSupport (apm_m00A04_partial φ i) := by
  unfold apm_m00A04_partial
  exact hφ.fderiv_apply ℝ (Pi.single i 1)

lemma apm_m00A04_partial_tsupport_subset {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ) (i : Fin n) :
    tsupport (apm_m00A04_partial φ i) ⊆ U :=
  (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hφ.2.2

lemma apm_m00A04_testFunction_L2On {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ) :
    apm_m00A04_L2On U φ := by
  unfold apm_m00A04_L2On
  have hcont : Continuous (fun x ↦ |φ x| ^ 2) :=
    (continuous_abs.comp hφ.1.continuous).pow 2
  have hsupp : HasCompactSupport (fun x ↦ |φ x| ^ 2) := by
    apply hφ.2.1.mono'
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    have hne : φ x ≠ 0 := fun h0 ↦ hx (by simp [h0])
    exact subset_tsupport φ (Function.mem_support.mpr hne)
  exact ⟨hφ.1.continuous.aestronglyMeasurable,
    hcont.integrable_of_hasCompactSupport hsupp |>.integrableOn⟩

lemma apm_m00A04_partial_L2On {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ) (i : Fin n) :
    apm_m00A04_L2On U (apm_m00A04_partial φ i) := by
  unfold apm_m00A04_L2On
  have hcont : Continuous (fun x ↦ |apm_m00A04_partial φ i x| ^ 2) :=
    (continuous_abs.comp (apm_m00A04_partial_continuous (hφ.1.of_le (by simp)) i)).pow 2
  have hsupp : HasCompactSupport (fun x ↦ |apm_m00A04_partial φ i x| ^ 2) := by
    apply (apm_m00A04_partial_hasCompactSupport hφ.2.1 i).mono'
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    have hne : apm_m00A04_partial φ i x ≠ 0 := fun h0 ↦ hx (by simp [h0])
    exact subset_tsupport _ (Function.mem_support.mpr hne)
  exact ⟨(apm_m00A04_partial_continuous (hφ.1.of_le (by simp)) i).aestronglyMeasurable,
    hcont.integrable_of_hasCompactSupport hsupp |>.integrableOn⟩

lemma apm_m00A04_testFunction_memLp {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ) :
    MemLp φ 2 (volume.restrict U) := by
  rw [memLp_two_iff_integrable_sq hφ.1.continuous.aestronglyMeasurable]
  have h := (apm_m00A04_testFunction_L2On hφ).2
  simpa only [sq_abs] using h

lemma apm_m00A04_partial_memLp {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ) (i : Fin n) :
    MemLp (apm_m00A04_partial φ i) 2 (volume.restrict U) := by
  rw [memLp_two_iff_integrable_sq
    (apm_m00A04_partial_continuous (hφ.1.of_le (by simp)) i).aestronglyMeasurable]
  have h := (apm_m00A04_partial_L2On hφ i).2
  simpa only [sq_abs] using h

/-- The encoded energy space: the `L²` class of the value together with the
`L²` classes of the partial derivatives, indexed by `Option (Fin n)` so that
the whole package carries the `PiLp` inner-product-space structure. -/
abbrev apm_m00A04_energySpace {n : ℕ} (U : Set (Fin n → ℝ)) : Type :=
  PiLp 2 (fun _ : Option (Fin n) ↦ Lp ℝ 2 (volume.restrict U))

/-- The energy-space element attached to a test function: its `L²` class
together with the `L²` classes of its partial derivatives. -/
noncomputable def apm_m00A04_testPair {n : ℕ} {U : Set (Fin n → ℝ)}
    (φ : (Fin n → ℝ) → ℝ) (hφ : apm_m00A04_testFunction U φ) :
    apm_m00A04_energySpace U :=
  WithLp.toLp 2 fun o : Option (Fin n) ↦ match o with
    | none => MemLp.toLp φ (apm_m00A04_testFunction_memLp hφ)
    | some i => MemLp.toLp (apm_m00A04_partial φ i)
        (apm_m00A04_partial_memLp hφ i)

/-- The submodule of the energy space generated by test pairs. -/
noncomputable def apm_m00A04_testSubmodule {n : ℕ} (U : Set (Fin n → ℝ)) :
    Submodule ℝ (apm_m00A04_energySpace U) :=
  Submodule.span ℝ
    (Set.range fun φ : {φ // apm_m00A04_testFunction U φ} ↦
      apm_m00A04_testPair φ φ.2)

/-- The encoded Sobolev space `H¹₀(U)`: the energy closure of the test
pairs. -/
noncomputable def apm_m00A04_H10 {n : ℕ} (U : Set (Fin n → ℝ)) :
    Submodule ℝ (apm_m00A04_energySpace U) :=
  (apm_m00A04_testSubmodule U).topologicalClosure

lemma apm_m00A04_testPair_mem {n : ℕ} {U : Set (Fin n → ℝ)}
    (φ : (Fin n → ℝ) → ℝ) (hφ : apm_m00A04_testFunction U φ) :
    apm_m00A04_testPair φ hφ ∈ apm_m00A04_H10 U :=
  Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨⟨φ, hφ⟩, rfl⟩)

lemma apm_m00A04_testFunction_zero {n : ℕ} {U : Set (Fin n → ℝ)} :
    apm_m00A04_testFunction U (0 : (Fin n → ℝ) → ℝ) := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · have hts : tsupport (0 : (Fin n → ℝ) → ℝ) = ∅ := by
      simp [tsupport, Function.support]
    show IsCompact (tsupport (0 : (Fin n → ℝ) → ℝ))
    rw [hts]
    exact isCompact_empty
  · show tsupport (0 : (Fin n → ℝ) → ℝ) ⊆ U
    simp [tsupport, Function.support]

lemma apm_m00A04_testPair_add {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ ψ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ)
    (hψ : apm_m00A04_testFunction U ψ) :
    apm_m00A04_testPair (φ + ψ) (apm_m00A04_testFunction_add hφ hψ) =
      apm_m00A04_testPair φ hφ + apm_m00A04_testPair ψ hψ := by
  apply PiLp.ext
  intro o
  cases o with
  | none =>
    exact MemLp.toLp_add (apm_m00A04_testFunction_memLp hφ)
      (apm_m00A04_testFunction_memLp hψ)
  | some i =>
    show MemLp.toLp (apm_m00A04_partial (φ + ψ) i)
        (apm_m00A04_partial_memLp (apm_m00A04_testFunction_add hφ hψ) i) =
      MemLp.toLp (apm_m00A04_partial φ i) (apm_m00A04_partial_memLp hφ i) +
        MemLp.toLp (apm_m00A04_partial ψ i) (apm_m00A04_partial_memLp hψ i)
    rw [← MemLp.toLp_add (apm_m00A04_partial_memLp hφ i)
      (apm_m00A04_partial_memLp hψ i)]
    apply MemLp.toLp_congr
    filter_upwards [] with x
    exact apm_m00A04_partial_add hφ.1 hψ.1 i x

lemma apm_m00A04_testPair_smul {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ : (Fin n → ℝ) → ℝ} (c : ℝ) (hc : c ≠ 0)
    (hφ : apm_m00A04_testFunction U φ) :
    apm_m00A04_testPair (c • φ) (apm_m00A04_testFunction_smul c hc hφ) =
      c • apm_m00A04_testPair φ hφ := by
  apply PiLp.ext
  intro o
  cases o with
  | none => exact MemLp.toLp_const_smul c (apm_m00A04_testFunction_memLp hφ)
  | some i =>
    show MemLp.toLp (apm_m00A04_partial (c • φ) i)
        (apm_m00A04_partial_memLp (apm_m00A04_testFunction_smul c hc hφ) i) =
      c • MemLp.toLp (apm_m00A04_partial φ i) (apm_m00A04_partial_memLp hφ i)
    rw [← MemLp.toLp_const_smul c (apm_m00A04_partial_memLp hφ i)]
    apply MemLp.toLp_congr
    filter_upwards [] with x
    simp [apm_m00A04_partial_smul φ hφ.1 c i x]

lemma apm_m00A04_testPair_zero {n : ℕ} {U : Set (Fin n → ℝ)} :
    apm_m00A04_testPair (0 : (Fin n → ℝ) → ℝ)
      (@apm_m00A04_testFunction_zero n U) = 0 := by
  apply PiLp.ext
  intro o
  cases o with
  | none =>
    exact MemLp.toLp_zero (apm_m00A04_testFunction_memLp
      (@apm_m00A04_testFunction_zero n U))
  | some i =>
    have h3 : apm_m00A04_partial (0 : (Fin n → ℝ) → ℝ) i = 0 := by
      funext x
      exact apm_m00A04_partial_zero i x
    have h4 : MemLp (apm_m00A04_partial (0 : (Fin n → ℝ) → ℝ) i)
        2 (volume.restrict U) :=
      apm_m00A04_partial_memLp (@apm_m00A04_testFunction_zero n U) i
    have h5 : MemLp (0 : (Fin n → ℝ) → ℝ) 2 (volume.restrict U) := h3 ▸ h4
    show MemLp.toLp _ h4 = 0
    rw [show MemLp.toLp _ h4 =
        MemLp.toLp (0 : (Fin n → ℝ) → ℝ) h5 from
      MemLp.toLp_congr _ _
        (Filter.Eventually.of_forall fun x ↦ apm_m00A04_partial_zero i x)]
    exact MemLp.toLp_zero h5

/-- Every element of the test submodule is itself a test pair: smooth
compactly supported functions are closed under the module operations. -/
lemma apm_m00A04_mem_testSubmodule_iff {n : ℕ} {U : Set (Fin n → ℝ)}
    (s : apm_m00A04_energySpace U) :
    s ∈ apm_m00A04_testSubmodule U ↔
      ∃ (φ : (Fin n → ℝ) → ℝ) (hφ : apm_m00A04_testFunction U φ),
        s = apm_m00A04_testPair φ hφ := by
  constructor
  · intro hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨φ, hφ⟩, rfl⟩ := hx
      exact ⟨φ, hφ, rfl⟩
    | zero =>
      exact ⟨0, apm_m00A04_testFunction_zero, apm_m00A04_testPair_zero.symm⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨φ, hφ, rfl⟩ := ihx
      obtain ⟨ψ, hψ, rfl⟩ := ihy
      exact ⟨φ + ψ, apm_m00A04_testFunction_add hφ hψ,
        (apm_m00A04_testPair_add hφ hψ).symm⟩
    | smul c x _ ihx =>
      obtain ⟨φ, hφ, rfl⟩ := ihx
      by_cases hc : c = 0
      · subst c
        refine ⟨0, apm_m00A04_testFunction_zero, ?_⟩
        rw [apm_m00A04_testPair_zero]
        simp
      · exact ⟨c • φ, apm_m00A04_testFunction_smul c hc hφ,
          (apm_m00A04_testPair_smul c hc hφ).symm⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact Submodule.subset_span ⟨⟨φ, hφ⟩, rfl⟩

/-- The coordinate-slice map used to reduce integration by parts to one
dimension. -/
lemma apm_m00A04_insertNth_eq (m : ℕ) (i : Fin (m + 1))
    (r : Fin m → ℝ) (t : ℝ) :
    (Fin.insertNth i t r : Fin (m + 1) → ℝ) =
      Fin.insertNth i 0 r + t • (Pi.single i 1 : Fin (m + 1) → ℝ) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [Fin.insertNth_apply_same, Pi.single_eq_same]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
    subst hk
    rw [Pi.add_apply, Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_succAbove, Pi.smul_apply,
      Pi.single_eq_of_ne (Fin.succAbove_ne i k)]
    simp

lemma apm_m00A04_hasDerivAt_insertNth (m : ℕ) (i : Fin (m + 1))
    (r : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun t ↦ (Fin.insertNth i t r : Fin (m + 1) → ℝ))
      (Pi.single i 1 : Fin (m + 1) → ℝ) t := by
  have hfun : (fun t ↦ (Fin.insertNth i t r : Fin (m + 1) → ℝ)) =
      (fun t : ℝ ↦ Fin.insertNth i 0 r +
        t • (Pi.single i 1 : Fin (m + 1) → ℝ)) := by
    funext t
    exact apm_m00A04_insertNth_eq m i r t
  rw [hfun]
  have h1 := ((hasDerivAt_id t).smul_const
    (Pi.single i 1 : Fin (m + 1) → ℝ)).const_add (Fin.insertNth i 0 r)
  simpa using h1

/-- The one-dimensional core of integration by parts: the derivative of a
compactly supported `C¹` function on the line integrates to zero. -/
lemma apm_m00A04_integral_deriv_eq_zero {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hcs : HasCompactSupport ψ) :
    ∫ t : ℝ, deriv ψ t = 0 := by
  have hderiv_cont : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hderiv_supp : HasCompactSupport (deriv ψ) := hcs.deriv
  have hderiv_int : Integrable (deriv ψ) :=
    hderiv_cont.integrable_of_hasCompactSupport hderiv_supp
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hcs.isBounded
  have hbound : ∀ t : ℝ, t ∈ tsupport ψ → |t| ≤ R := by
    intro t ht
    have h2 := hR ht
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    exact h2
  have hzero : ∀ t : ℝ, |t| > R → ψ t = 0 := by
    intro t ht
    by_contra hne
    have hts : t ∈ tsupport ψ :=
      subset_tsupport ψ (Function.mem_support.mpr hne)
    exact absurd (hbound t hts) (not_le.mpr ht)
  have hbot : Filter.Tendsto ψ Filter.atBot (nhds 0) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.eventually_lt_atBot (-R)] with t ht
    have habs : |t| > R := lt_of_lt_of_le (by linarith) (neg_le_abs t)
    exact (hzero t habs).symm
  have htop : Filter.Tendsto ψ Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop R] with t ht
    have habs : |t| > R := lt_of_lt_of_le ht (le_abs_self t)
    exact (hzero t habs).symm
  have h := integral_of_hasDerivAt_of_tendsto
    (fun t ↦ (hψ.differentiable (by simp)).differentiableAt.hasDerivAt)
    hderiv_int hbot htop
  simpa using h

/-- The integral of a partial derivative of a compactly supported `C¹`
function over the whole space vanishes. -/
lemma apm_m00A04_integral_partial_eq_zero {n : ℕ} (i : Fin n)
    {θ : (Fin n → ℝ) → ℝ} (hθ : ContDiff ℝ 1 θ)
    (hcs : HasCompactSupport θ) :
    ∫ x, apm_m00A04_partial θ i x = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    set e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) i).symm
      with he
    have hmp : MeasurePreserving (⇑e)
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))
        (volume : Measure (Fin (m + 1) → ℝ)) :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) i).symm
    have hcont : Continuous (apm_m00A04_partial θ i) :=
      apm_m00A04_partial_continuous hθ i
    have hint : Integrable (apm_m00A04_partial θ i) :=
      hcont.integrable_of_hasCompactSupport
        (apm_m00A04_partial_hasCompactSupport hcs i)
    have hint' : Integrable
        (fun p : ℝ × (Fin m → ℝ) ↦ apm_m00A04_partial θ i (e p))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
      have h := hint
      rw [← hmp.map_eq] at h
      have h2 := (integrable_map_equiv e (apm_m00A04_partial θ i)).mp h
      simpa [Function.comp_def] using h2
    have hzero : ∀ r : Fin m → ℝ,
        ∫ t : ℝ, apm_m00A04_partial θ i (e (t, r)) = 0 := by
      intro r
      have hsymm : ∀ (t : ℝ),
          e (t, r) = (Fin.insertNth i t r : Fin (m + 1) → ℝ) := fun t ↦ rfl
      set ψ : ℝ → ℝ := fun t ↦ θ (Fin.insertNth i t r) with hψdef
      have hderiv : ∀ t : ℝ,
          HasDerivAt ψ (apm_m00A04_partial θ i (Fin.insertNth i t r)) t := by
        intro t
        have hθd : HasFDerivAt θ (fderiv ℝ θ (Fin.insertNth i t r))
            (Fin.insertNth i t r) :=
          (hθ.differentiable (by simp)).differentiableAt.hasFDerivAt
        have hcomp := hθd.comp_hasDerivAt t
          (apm_m00A04_hasDerivAt_insertNth m i r t)
        exact hcomp
      have hψcont : ContDiff ℝ 1 ψ := by
        have hg : ContDiff ℝ 1
            (fun t : ℝ ↦ t • (Pi.single i 1 : Fin (m + 1) → ℝ)) :=
          (contDiff_id (𝕜 := ℝ) (n := 1)).smul contDiff_const
        have h2 : ContDiff ℝ 1
            (fun t : ℝ ↦ (Fin.insertNth i 0 r : Fin (m + 1) → ℝ) +
              t • (Pi.single i 1 : Fin (m + 1) → ℝ)) :=
          contDiff_const.add hg
        rw [show (fun t : ℝ ↦ (Fin.insertNth i 0 r : Fin (m + 1) → ℝ) +
                t • (Pi.single i 1 : Fin (m + 1) → ℝ)) =
              (fun t ↦ (Fin.insertNth i t r : Fin (m + 1) → ℝ)) from
            funext fun t ↦ (apm_m00A04_insertNth_eq m i r t).symm] at h2
        exact hθ.comp h2
      have hR : ∃ R : ℝ, ∀ x : Fin (m + 1) → ℝ, x ∈ tsupport θ →
          |x i| ≤ R := by
        have himg : IsCompact
            ((fun x : Fin (m + 1) → ℝ ↦ x i) '' tsupport θ) :=
          hcs.image (continuous_apply i)
        obtain ⟨a, ha⟩ := himg.isBounded.bddAbove
        obtain ⟨b, hb⟩ := himg.isBounded.bddBelow
        refine ⟨max a (-b), fun x hx ↦ ?_⟩
        have h1 : x i ≤ a := ha (Set.mem_image_of_mem _ hx)
        have h2 : b ≤ x i := hb (Set.mem_image_of_mem _ hx)
        rw [abs_le]
        constructor <;> linarith [le_max_left a (-b), le_max_right a (-b)]
      obtain ⟨R, hR⟩ := hR
      have hsuppψ : Function.support ψ ⊆ Metric.closedBall 0 R := by
        intro t ht
        rw [Function.mem_support] at ht
        have h1 : Fin.insertNth i t r ∈ tsupport θ :=
          subset_tsupport θ (Function.mem_support.mpr ht)
        have h2 := hR _ h1
        rw [Fin.insertNth_apply_same] at h2
        rw [Metric.mem_closedBall, dist_zero_right]
        exact h2
      have htsψ : tsupport ψ ⊆ Metric.closedBall 0 R :=
        closure_minimal hsuppψ Metric.isClosed_closedBall
      have hcsψ : HasCompactSupport ψ :=
        (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure htsψ
      have hslice : ∫ t : ℝ, deriv ψ t = 0 :=
        apm_m00A04_integral_deriv_eq_zero hψcont hcsψ
      have heq : ∀ t : ℝ, apm_m00A04_partial θ i (e (t, r)) = deriv ψ t := by
        intro t
        rw [hsymm t]
        exact ((hderiv t).deriv).symm
      rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
      exact hslice
    rw [← hmp.map_eq, integral_map_equiv]
    calc ∫ x : ℝ × (Fin m → ℝ), apm_m00A04_partial θ i (e x)
            ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))
        = ∫ r : Fin m → ℝ, ∫ t : ℝ, apm_m00A04_partial θ i (e (t, r)) :=
          integral_prod_symm _ hint'
      _ = 0 := by simp [hzero]

/-- Integration by parts for pairs of smooth compactly supported test
functions, integrated over the whole space. -/
lemma apm_m00A04_integral_partial_mul {n : ℕ} {U : Set (Fin n → ℝ)}
    {φ ψ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ)
    (hψ : apm_m00A04_testFunction U ψ) (i : Fin n) :
    ∫ x, apm_m00A04_partial φ i x * ψ x =
      -∫ x, φ x * apm_m00A04_partial ψ i x := by
  have hprod_diff : ContDiff ℝ ∞ (φ * ψ) := hφ.1.mul hψ.1
  have hprod_supp : HasCompactSupport (φ * ψ) := by
    apply hφ.2.1.mono'
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    have hne : φ x ≠ 0 := fun h0 ↦ hx (by simp [h0])
    exact subset_tsupport φ (Function.mem_support.mpr hne)
  have hθ : ∫ x, apm_m00A04_partial (φ * ψ) i x = 0 :=
    apm_m00A04_integral_partial_eq_zero i
      (hprod_diff.of_le (by simp)) hprod_supp
  have hprodrule : ∀ x, apm_m00A04_partial (φ * ψ) i x =
      apm_m00A04_partial φ i x * ψ x + φ x * apm_m00A04_partial ψ i x := by
    intro x
    unfold apm_m00A04_partial
    rw [fderiv_mul
      (hφ.1.differentiable (by simp)).differentiableAt
      (hψ.1.differentiable (by simp)).differentiableAt]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  have hint1 : Integrable (fun x ↦ apm_m00A04_partial φ i x * ψ x) :=
    ((apm_m00A04_partial_continuous (hφ.1.of_le (by simp)) i).mul
      hψ.1.continuous).integrable_of_hasCompactSupport (by
        apply hψ.2.1.mono'
        intro x hx
        simp only [Function.mem_support, ne_eq] at hx
        have hne : ψ x ≠ 0 := fun h0 ↦ hx (by simp [h0])
        exact subset_tsupport ψ (Function.mem_support.mpr hne))
  have hint2 : Integrable (fun x ↦ φ x * apm_m00A04_partial ψ i x) :=
    (hφ.1.continuous.mul
      (apm_m00A04_partial_continuous (hψ.1.of_le (by simp)) i)
      ).integrable_of_hasCompactSupport (by
        apply hφ.2.1.mono'
        intro x hx
        simp only [Function.mem_support, ne_eq] at hx
        have hne : φ x ≠ 0 := fun h0 ↦ hx (by simp [h0])
        exact subset_tsupport φ (Function.mem_support.mpr hne))
  have hsplit : ∫ x, apm_m00A04_partial (φ * ψ) i x =
      (∫ x, apm_m00A04_partial φ i x * ψ x) +
        ∫ x, φ x * apm_m00A04_partial ψ i x := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hprodrule)]
    exact integral_add hint1 hint2
  rw [hsplit] at hθ
  linarith

/-- Integrals against `volume.restrict U` of functions vanishing outside
`U` agree with the integral over the whole space. -/
lemma apm_m00A04_integral_restrict_eq {n : ℕ} {U : Set (Fin n → ℝ)}
    (hUopen : IsOpen U) {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f) (hsupp : ∀ x ∉ U, f x = 0) :
    ∫ x, f x ∂(volume.restrict U) = ∫ x, f x := by
  have h2 : ∫ x in Uᶜ, f x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hUopen.measurableSet.compl] with x hx
    exact hsupp x hx
  show ∫ x in U, f x = ∫ x, f x
  rw [← integral_add_compl hUopen.measurableSet hf, h2, add_zero]

/-- Integration by parts for test functions, with integrals taken over
`U`. -/
lemma apm_m00A04_integral_partial_mul_restrict {n : ℕ} {U : Set (Fin n → ℝ)}
    (hUopen : IsOpen U)
    {φ ψ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ)
    (hψ : apm_m00A04_testFunction U ψ) (i : Fin n) :
    ∫ x, apm_m00A04_partial ψ i x * φ x ∂(volume.restrict U) =
      -∫ x, ψ x * apm_m00A04_partial φ i x ∂(volume.restrict U) := by
  have hint1 : Integrable (fun x ↦ apm_m00A04_partial ψ i x * φ x) :=
    ((apm_m00A04_partial_continuous (hψ.1.of_le (by simp)) i).mul
      hφ.1.continuous).integrable_of_hasCompactSupport (by
        apply hφ.2.1.mono'
        intro x hx
        simp only [Function.mem_support, ne_eq] at hx
        have hne : φ x ≠ 0 := fun h0 ↦ hx (by simp [h0])
        exact subset_tsupport φ (Function.mem_support.mpr hne))
  have hint2 : Integrable (fun x ↦ ψ x * apm_m00A04_partial φ i x) :=
    (hψ.1.continuous.mul
      (apm_m00A04_partial_continuous (hφ.1.of_le (by simp)) i)
      ).integrable_of_hasCompactSupport (by
        apply hψ.2.1.mono'
        intro x hx
        simp only [Function.mem_support, ne_eq] at hx
        have hne : ψ x ≠ 0 := fun h0 ↦ hx (by simp [h0])
        exact subset_tsupport ψ (Function.mem_support.mpr hne))
  have hsupp1 : ∀ x ∉ U, apm_m00A04_partial ψ i x * φ x = 0 := by
    intro x hx
    have hφ0 : φ x = 0 := by
      by_contra hne
      exact hx (hφ.2.2 (subset_tsupport φ (Function.mem_support.mpr hne)))
    simp [hφ0]
  have hsupp2 : ∀ x ∉ U, ψ x * apm_m00A04_partial φ i x = 0 := by
    intro x hx
    have hψ0 : ψ x = 0 := by
      by_contra hne
      exact hx (hψ.2.2 (subset_tsupport ψ (Function.mem_support.mpr hne)))
    simp [hψ0]
  rw [apm_m00A04_integral_restrict_eq hUopen hint1 hsupp1,
    apm_m00A04_integral_restrict_eq hUopen hint2 hsupp2]
  exact apm_m00A04_integral_partial_mul hψ hφ i

/-- Inner product of an `L²` class with the class of an `L²` function is
the integral of the product. -/
lemma apm_m00A04_inner_toLp {n : ℕ} {U : Set (Fin n → ℝ)}
    (a : Lp ℝ 2 (volume.restrict U)) {ψ : (Fin n → ℝ) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict U)) :
    ⟪a, MemLp.toLp ψ hψ⟫ = ∫ x in U, a x * ψ x := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hψ] with x hx
  rw [hx]
  exact RCLike.inner_apply' _ _

/-- Inner product of the class of an `L²` function with an `L²` class is
the integral of the product. -/
lemma apm_m00A04_toLp_inner {n : ℕ} {U : Set (Fin n → ℝ)}
    (a : Lp ℝ 2 (volume.restrict U)) {ψ : (Fin n → ℝ) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict U)) :
    ⟪MemLp.toLp ψ hψ, a⟫ = ∫ x in U, ψ x * a x := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hψ] with x hx
  rw [hx]
  exact RCLike.inner_apply' _ _

/-- The squared energy norm is the sum of the squared `L²` norms of the
value and of the partials. -/
lemma apm_m00A04_energy_norm_sq {n : ℕ} {U : Set (Fin n → ℝ)}
    (w : apm_m00A04_energySpace U) :
    ‖w‖ ^ 2 = (∫ x in U, (w none x) ^ 2) +
      ∑ i : Fin n, ∫ x in U, (w (some i) x) ^ 2 := by
  have hcomp : ∀ a : Lp ℝ 2 (volume.restrict U),
      ⟪a, a⟫ = ∫ x in U, (a x) ^ 2 := by
    intro a
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards with x
    rw [pow_two]
    exact RCLike.inner_apply' _ _
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fintype.sum_option,
    hcomp (w none),
    Finset.sum_congr rfl (fun i _ ↦ hcomp (w (some i)))]

/-- The Riesz representative in the encoded `H¹₀(U)` of the forcing
functional `w ↦ ∫ F · w`. -/
lemma apm_m00A04_riesz_element {n : ℕ} {U : Set (Fin n → ℝ)}
    (F : (Fin n → ℝ) → ℝ) (hF : apm_m00A04_L2On U F) :
    ∃ w0 : apm_m00A04_energySpace U,
      w0 ∈ apm_m00A04_H10 U ∧
      ∀ w : apm_m00A04_energySpace U, w ∈ apm_m00A04_H10 U →
        ⟪w0, w⟫ = ∫ x in U, F x * w none x := by
  have hFmem : MemLp F 2 (volume.restrict U) := by
    rw [memLp_two_iff_integrable_sq hF.1]
    simpa only [sq_abs] using hF.2
  set e0 : Lp ℝ 2 (volume.restrict U) := MemLp.toLp F hFmem with he0
  set e0E : apm_m00A04_energySpace U :=
    WithLp.toLp 2 fun o : Option (Fin n) ↦ match o with
      | none => e0
      | some _ => (0 : Lp ℝ 2 (volume.restrict U)) with he0E
  set ℓ : (apm_m00A04_H10 U) →L[ℝ] ℝ :=
    (innerSL ℝ e0E).comp (apm_m00A04_H10 U).subtypeL with hℓ
  haveI hCS : CompleteSpace ↥(apm_m00A04_H10 U) :=
    Submodule.topologicalClosure.completeSpace _
  set uH : ↥(apm_m00A04_H10 U) :=
    (@InnerProductSpace.toDual ℝ ↥(apm_m00A04_H10 U) _ _ _ hCS).symm ℓ with huH
  refine ⟨(uH : apm_m00A04_energySpace U), uH.2, ?_⟩
  intro w hw
  have h1 : ⟪(uH : apm_m00A04_energySpace U), w⟫ = ℓ ⟨w, hw⟩ :=
    @InnerProductSpace.toDual_symm_apply ℝ ↥(apm_m00A04_H10 U) _ _ _ hCS
      ⟨w, hw⟩ ℓ
  have h2 : ℓ ⟨w, hw⟩ = ⟪e0E, w⟫ := by
    simp only [hℓ, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, innerSL_apply]
  rw [h1, h2, PiLp.inner_apply, Fintype.sum_option]
  have hsum : ∑ i : Fin n, ⟪e0E (some i), w (some i)⟫ = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    show ⟪(0 : Lp ℝ 2 (volume.restrict U)), w (some i)⟫ = 0
    exact inner_zero_left _
  rw [hsum, add_zero]
  show ⟪e0, w none⟫ = ∫ x in U, F x * w none x
  exact apm_m00A04_toLp_inner (w none) hFmem

/-- Inner product of the classes of two `L²` functions is the integral of
their product. -/
lemma apm_m00A04_toLp_inner_toLp {n : ℕ} {U : Set (Fin n → ℝ)}
    {ψ θ : (Fin n → ℝ) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict U))
    (hθ : MemLp θ 2 (volume.restrict U)) :
    ⟪MemLp.toLp ψ hψ, MemLp.toLp θ hθ⟫ = ∫ x in U, ψ x * θ x := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hψ, MemLp.coeFn_toLp hθ] with x h1x h2x
  rw [h1x, h2x]
  exact RCLike.inner_apply' _ _

/-- The squared energy distance to a test pair, as the sum of the squared
`L²` distances of value and partials. -/
lemma apm_m00A04_energy_norm_sq_sub_testPair {n : ℕ} {U : Set (Fin n → ℝ)}
    (w : apm_m00A04_energySpace U) (φ : (Fin n → ℝ) → ℝ)
    (hφ : apm_m00A04_testFunction U φ) :
    ‖w - apm_m00A04_testPair φ hφ‖ ^ 2 =
      (∫ x in U, |w none x - φ x| ^ 2) +
        ∑ i : Fin n, ∫ x in U,
          |w (some i) x - apm_m00A04_partial φ i x| ^ 2 := by
  have h1 : ∀ (a : Lp ℝ 2 (volume.restrict U)) (ψ : (Fin n → ℝ) → ℝ)
      (hψ : MemLp ψ 2 (volume.restrict U)),
      (∫ x in U, ((a - MemLp.toLp ψ hψ) x) ^ 2) =
        ∫ x in U, |a x - ψ x| ^ 2 := by
    intro a ψ hψ
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub a (MemLp.toLp ψ hψ),
      MemLp.coeFn_toLp hψ] with x hsub hx
    rw [hsub, Pi.sub_apply, hx, sq_abs]
  rw [apm_m00A04_energy_norm_sq]
  simp only [PiLp.sub_apply]
  rw [show (apm_m00A04_testPair φ hφ) none =
      MemLp.toLp φ (apm_m00A04_testFunction_memLp hφ) from rfl, h1]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show (apm_m00A04_testPair φ hφ) (some i) =
      MemLp.toLp (apm_m00A04_partial φ i)
        (apm_m00A04_partial_memLp hφ i) from rfl]
  exact h1 _ _ _

/-- The key orthogonality behind the weak-gradient identity: integration by
parts against test functions. -/
lemma apm_m00A04_testPair_ibp_inner {n : ℕ} {U : Set (Fin n → ℝ)}
    (hUopen : IsOpen U)
    {φ ψ : (Fin n → ℝ) → ℝ} (hφ : apm_m00A04_testFunction U φ)
    (hψ : apm_m00A04_testFunction U ψ) (i : Fin n) :
    ⟪MemLp.toLp (apm_m00A04_partial φ i) (apm_m00A04_partial_memLp hφ i),
      MemLp.toLp ψ (apm_m00A04_testFunction_memLp hψ)⟫ +
    ⟪MemLp.toLp φ (apm_m00A04_testFunction_memLp hφ),
      MemLp.toLp (apm_m00A04_partial ψ i)
        (apm_m00A04_partial_memLp hψ i)⟫ = 0 := by
  rw [apm_m00A04_toLp_inner_toLp, apm_m00A04_toLp_inner_toLp]
  have hibp := apm_m00A04_integral_partial_mul_restrict hUopen hψ hφ i
  have e1 : (∫ x in U, apm_m00A04_partial ψ i x * φ x) =
      ∫ x in U, φ x * apm_m00A04_partial ψ i x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm]
  have e2 : (∫ x in U, ψ x * apm_m00A04_partial φ i x) =
      ∫ x in U, apm_m00A04_partial φ i x * ψ x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm]
  linarith

/-- The weak-gradient identity for the components of an `H10` element:
integration by parts passes to the energy closure because the kernel of a
continuous linear functional is closed. -/
lemma apm_m00A04_weakGradient_of_H10 {n : ℕ} {U : Set (Fin n → ℝ)}
    (hUopen : IsOpen U) {w0 : apm_m00A04_energySpace U}
    (hw0H : w0 ∈ apm_m00A04_H10 U) :
    apm_m00A04_weakGradient U (fun x ↦ w0 none x)
      (fun i x ↦ w0 (some i) x) := by
  intro i φ hφ
  simp only []
  show (∫ x in U, w0 none x * apm_m00A04_partial φ i x) =
    -∫ x in U, w0 (some i) x * φ x
  have hφm := apm_m00A04_testFunction_memLp hφ
  have hdm := apm_m00A04_partial_memLp hφ i
  set j : apm_m00A04_energySpace U :=
    WithLp.toLp 2 fun o : Option (Fin n) ↦ match o with
      | none => MemLp.toLp (apm_m00A04_partial φ i) hdm
      | some k => if k = i then MemLp.toLp φ hφm
        else (0 : Lp ℝ 2 (volume.restrict U)) with hj
  have hperp : apm_m00A04_testSubmodule U ≤ (innerSL ℝ j).ker := by
    apply Submodule.span_le.mpr
    rintro - ⟨⟨ψ, hψ⟩, rfl⟩
    show innerSL ℝ j (apm_m00A04_testPair ψ hψ) = 0
    rw [innerSL_apply, PiLp.inner_apply, Fintype.sum_option]
    have h1 : (apm_m00A04_testPair ψ hψ) none =
        MemLp.toLp ψ (apm_m00A04_testFunction_memLp hψ) := rfl
    have h2 : ∀ k : Fin n, (apm_m00A04_testPair ψ hψ) (some k) =
        MemLp.toLp (apm_m00A04_partial ψ k)
          (apm_m00A04_partial_memLp hψ k) := fun k ↦ rfl
    have hjnone : j none = MemLp.toLp (apm_m00A04_partial φ i) hdm := rfl
    have hjapp : ∀ k : Fin n, j (some k) =
        (if k = i then MemLp.toLp φ hφm
          else (0 : Lp ℝ 2 (volume.restrict U))) := fun k ↦ rfl
    rw [hjnone, h1, Finset.sum_congr rfl (fun k _ ↦ by rw [hjapp k, h2 k])]
    rw [Finset.sum_eq_single i
      (fun k _ hki ↦ by rw [if_neg hki]; exact inner_zero_left _)
      (fun hi ↦ (hi (Finset.mem_univ i)).elim), if_pos rfl]
    exact apm_m00A04_testPair_ibp_inner hUopen hφ hψ i
  have hker : apm_m00A04_H10 U ≤ (innerSL ℝ j).ker :=
    Submodule.topologicalClosure_minimal _ hperp
      (ContinuousLinearMap.isClosed_ker _)
  have hj0 : innerSL ℝ j w0 = 0 := hker hw0H
  rw [innerSL_apply, PiLp.inner_apply, Fintype.sum_option] at hj0
  have hjnone : j none = MemLp.toLp (apm_m00A04_partial φ i) hdm := rfl
  have hjapp : ∀ k : Fin n, j (some k) =
      (if k = i then MemLp.toLp φ hφm
        else (0 : Lp ℝ 2 (volume.restrict U))) := fun k ↦ rfl
  rw [hjnone, Finset.sum_congr rfl (fun k _ ↦ by rw [hjapp k])] at hj0
  rw [Finset.sum_eq_single i
    (fun k _ hki ↦ by rw [if_neg hki]; exact inner_zero_left _)
    (fun hi ↦ (hi (Finset.mem_univ i)).elim), if_pos rfl] at hj0
  rw [apm_m00A04_toLp_inner, apm_m00A04_toLp_inner] at hj0
  have e1 : (∫ x in U, w0 none x * apm_m00A04_partial φ i x) =
      ∫ x in U, apm_m00A04_partial φ i x * w0 none x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm]
  have e2 : (∫ x in U, w0 (some i) x * φ x) =
      ∫ x in U, φ x * w0 (some i) x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm]
  linarith

/-- The energy approximation clause: points of `H10` are energy-norm limits
of test pairs, restated with the frozen raw-function presentation. -/
lemma apm_m00A04_energy_approx_of_H10 {n : ℕ} {U : Set (Fin n → ℝ)}
    {w0 : apm_m00A04_energySpace U} (hw0H : w0 ∈ apm_m00A04_H10 U) :
    ∀ ε : ℝ, 0 < ε → ∃ φ : (Fin n → ℝ) → ℝ,
      apm_m00A04_testFunction U φ ∧
      (∫ x in U, |w0 none x - φ x| ^ 2 +
        ∑ i : Fin n, |w0 (some i) x - apm_m00A04_partial φ i x| ^ 2) < ε := by
  intro ε hε
  have hmem : w0 ∈ closure ((apm_m00A04_testSubmodule U :
      Submodule ℝ (apm_m00A04_energySpace U)) :
      Set (apm_m00A04_energySpace U)) := by
    have h1 : w0 ∈ ((apm_m00A04_testSubmodule U).topologicalClosure :
        Set (apm_m00A04_energySpace U)) := hw0H
    rwa [Submodule.topologicalClosure_coe] at h1
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨y, hy, hdist⟩ := hmem (√ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨φ, hφ, rfl⟩ := (apm_m00A04_mem_testSubmodule_iff y).mp hy
  refine ⟨φ, hφ, ?_⟩
  have h2 : ‖w0 - apm_m00A04_testPair φ hφ‖ < √ε := by
    rw [← dist_eq_norm]
    exact hdist
  have hnorm : ‖w0 - apm_m00A04_testPair φ hφ‖ ^ 2 < ε := by
    nlinarith [Real.sq_sqrt (le_of_lt hε),
      norm_nonneg (w0 - apm_m00A04_testPair φ hφ),
      Real.sqrt_pos.mpr hε, h2]
  rw [apm_m00A04_energy_norm_sq_sub_testPair] at hnorm
  have hint0 : Integrable (fun x ↦ |w0 none x - φ x| ^ 2)
      (volume.restrict U) := by
    have hm : MemLp (fun x ↦ w0 none x - φ x) 2 (volume.restrict U) := by
      have h := (Lp.memLp (w0 none)).sub (apm_m00A04_testFunction_memLp hφ)
      simpa only [Pi.sub_apply] using h
    have h := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
    simpa only [sq_abs] using h
  have hint1 : ∀ i : Fin n, Integrable
      (fun x ↦ |w0 (some i) x - apm_m00A04_partial φ i x| ^ 2)
      (volume.restrict U) := fun i ↦ by
    have hm : MemLp (fun x ↦ w0 (some i) x - apm_m00A04_partial φ i x) 2
        (volume.restrict U) := by
      have h := (Lp.memLp (w0 (some i))).sub (apm_m00A04_partial_memLp hφ i)
      simpa only [Pi.sub_apply] using h
    have h := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
    simpa only [sq_abs] using h
  have hfun : (∫ x in U, |w0 none x - φ x| ^ 2 +
      ∑ i : Fin n, |w0 (some i) x - apm_m00A04_partial φ i x| ^ 2) =
      (∫ x in U, |w0 none x - φ x| ^ 2) +
        ∑ i : Fin n, ∫ x in U,
          |w0 (some i) x - apm_m00A04_partial φ i x| ^ 2 := by
    rw [integral_add hint0 (integrable_finset_sum _ fun i _ ↦ hint1 i),
      integral_finset_sum _ (fun i _ ↦ hint1 i)]
  rw [hfun]
  exact hnorm

/-- The variational identity descends from the energy closure to arbitrary
`H¹₀` representatives: approximate the representative by test pairs and use
the Riesz equation on the limit. -/
lemma apm_m00A04_variational_of_riesz {n : ℕ} {U : Set (Fin n → ℝ)}
    (F : (Fin n → ℝ) → ℝ)
    {w0 : apm_m00A04_energySpace U}
    (hw0var : ∀ w : apm_m00A04_energySpace U, w ∈ apm_m00A04_H10 U →
      ⟪w0, w⟫ = ∫ x in U, F x * w none x)
    {v : (Fin n → ℝ) → ℝ} {h : Fin n → (Fin n → ℝ) → ℝ}
    (hv : apm_m00A04_memH10WithGradient U v h) :
    (∫ x in U, (∑ i : Fin n, w0 (some i) x * h i x) + w0 none x * v x) =
      ∫ x in U, F x * v x := by
  obtain ⟨hvL2, hhL2, hvweak, hvapprox⟩ := hv
  have hvm : MemLp v 2 (volume.restrict U) := by
    rw [memLp_two_iff_integrable_sq hvL2.1]
    simpa only [sq_abs] using hvL2.2
  have hhm : ∀ i, MemLp (h i) 2 (volume.restrict U) := fun i ↦ by
    rw [memLp_two_iff_integrable_sq (hhL2 i).1]
    simpa only [sq_abs] using (hhL2 i).2
  set V : apm_m00A04_energySpace U :=
    WithLp.toLp 2 fun o : Option (Fin n) ↦ match o with
      | none => MemLp.toLp v hvm
      | some i => MemLp.toLp (h i) (hhm i) with hV
  have hVin : V ∈ closure ((apm_m00A04_testSubmodule U :
      Submodule ℝ (apm_m00A04_energySpace U)) :
      Set (apm_m00A04_energySpace U)) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨ψ, hψ, happrox⟩ := hvapprox (δ ^ 2) (by positivity)
    have hintv : Integrable (fun x ↦ |v x - ψ x| ^ 2)
        (volume.restrict U) := by
      have hm : MemLp (fun x ↦ v x - ψ x) 2 (volume.restrict U) :=
        hvm.sub (apm_m00A04_testFunction_memLp hψ)
      have h := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
      simpa only [sq_abs] using h
    have hinth : ∀ i : Fin n, Integrable
        (fun x ↦ |h i x - apm_m00A04_partial ψ i x| ^ 2)
        (volume.restrict U) := fun i ↦ by
      have hm : MemLp (fun x ↦ h i x - apm_m00A04_partial ψ i x) 2
          (volume.restrict U) :=
        (hhm i).sub (apm_m00A04_partial_memLp hψ i)
      have h := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
      simpa only [sq_abs] using h
    have hsplit : (∫ x in U, |v x - ψ x| ^ 2 +
        ∑ i : Fin n, |h i x - apm_m00A04_partial ψ i x| ^ 2) =
        (∫ x in U, |v x - ψ x| ^ 2) +
          ∑ i : Fin n, ∫ x in U,
            |h i x - apm_m00A04_partial ψ i x| ^ 2 := by
      rw [integral_add hintv (integrable_finset_sum _ fun i _ ↦ hinth i),
        integral_finset_sum _ (fun i _ ↦ hinth i)]
    rw [hsplit] at happrox
    refine ⟨apm_m00A04_testPair ψ hψ,
      Submodule.subset_span ⟨⟨ψ, hψ⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have h2 : ‖V - apm_m00A04_testPair ψ hψ‖ ^ 2 < δ ^ 2 := by
      rw [apm_m00A04_energy_norm_sq_sub_testPair]
      have e1 : (∫ x in U, |V none x - ψ x| ^ 2) =
          ∫ x in U, |v x - ψ x| ^ 2 := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hvm] with x hx
        rw [show V none = MemLp.toLp v hvm from rfl, hx]
      have e2 : ∀ i : Fin n,
          (∫ x in U, |V (some i) x - apm_m00A04_partial ψ i x| ^ 2) =
          ∫ x in U, |h i x - apm_m00A04_partial ψ i x| ^ 2 := fun i ↦ by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp (hhm i)] with x hx
        rw [show V (some i) = MemLp.toLp (h i) (hhm i) from rfl, hx]
      rw [e1, Finset.sum_congr rfl (fun i _ ↦ e2 i)]
      exact happrox
    nlinarith [h2, norm_nonneg (V - apm_m00A04_testPair ψ hψ), hδ]
  have hVH : V ∈ apm_m00A04_H10 U := by
    have hsub : closure ((apm_m00A04_testSubmodule U :
        Submodule ℝ (apm_m00A04_energySpace U)) :
        Set (apm_m00A04_energySpace U)) ⊆
        ((apm_m00A04_H10 U : Submodule ℝ (apm_m00A04_energySpace U)) :
        Set (apm_m00A04_energySpace U)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact Subset.rfl
    exact hsub hVin
  have hvar := hw0var V hVH
  rw [PiLp.inner_apply, Fintype.sum_option] at hvar
  have e0 : ⟪w0 none, V none⟫ = ∫ x in U, w0 none x * v x := by
    rw [show V none = MemLp.toLp v hvm from rfl]
    exact apm_m00A04_inner_toLp (w0 none) hvm
  have ei : ∀ i : Fin n, ⟪w0 (some i), V (some i)⟫ =
      ∫ x in U, w0 (some i) x * h i x := fun i ↦ by
    rw [show V (some i) = MemLp.toLp (h i) (hhm i) from rfl]
    exact apm_m00A04_inner_toLp (w0 (some i)) (hhm i)
  rw [e0, Finset.sum_congr rfl (fun i _ ↦ ei i)] at hvar
  have hrv : (∫ x in U, F x * V none x) = ∫ x in U, F x * v x := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hvm] with x hx
    rw [show V none = MemLp.toLp v hvm from rfl, hx]
  rw [hrv] at hvar
  have hi0 : Integrable (fun x ↦ w0 none x * v x)
      (volume.restrict U) :=
    (Lp.memLp _).integrable_mul hvm
  have hii : ∀ i : Fin n, Integrable (fun x ↦ w0 (some i) x * h i x)
      (volume.restrict U) :=
    fun i ↦ (Lp.memLp _).integrable_mul (hhm i)
  rw [← hvar, integral_add (integrable_finset_sum _ fun i _ ↦ hii i) hi0,
    integral_finset_sum _ (fun i _ ↦ hii i)]
  exact add_comm _ _

/-- The positive-dimensional representative form of the Lax--Milgram theorem
needed by `apm_m00a04`.  Its proof constructs the energy completion of
compactly supported smooth functions and identifies completion points with the
raw function/weak-gradient pairs in `apm_m00A04_memH10WithGradient`. -/
theorem apm_m00A04_positive_dimensional_weak_solution
    {n : ℕ} (hn : n ≠ 0) (U : Set (Fin n → ℝ))
    (hUne : U.Nonempty) (hUopen : IsOpen U)
    (hUbounded : Bornology.IsBounded U)
    (F : (Fin n → ℝ) → ℝ) (hF : apm_m00A04_L2On U F) (hF0 : F ≠ 0) :
    ∃ (u : (Fin n → ℝ) → ℝ)
      (g : Fin n → (Fin n → ℝ) → ℝ),
      apm_m00A04_memH10WithGradient U u g ∧
      ∀ (v : (Fin n → ℝ) → ℝ)
        (h : Fin n → (Fin n → ℝ) → ℝ),
        apm_m00A04_memH10WithGradient U v h →
          (∫ x in U, (∑ i : Fin n, g i x * h i x) + u x * v x) =
            ∫ x in U, F x * v x := by
  obtain ⟨w0, hw0H, hw0var⟩ := apm_m00A04_riesz_element F hF
  have hL2 : ∀ o : Option (Fin n),
      apm_m00A04_L2On U (fun x ↦ w0 o x) := fun o ↦ by
    have hm : MemLp (fun x ↦ w0 o x) 2 (volume.restrict U) := Lp.memLp _
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    have hi := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
    simpa only [sq_abs] using hi
  refine ⟨fun x ↦ w0 none x, fun i x ↦ w0 (some i) x,
    ⟨hL2 none, fun i ↦ hL2 (some i),
      apm_m00A04_weakGradient_of_H10 hUopen hw0H,
      apm_m00A04_energy_approx_of_H10 hw0H⟩,
    fun v h hv ↦ apm_m00A04_variational_of_riesz F hw0var hv⟩

theorem apm_m00a04
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V →L[ℝ] ℝ) :
    BddBelow (range (apm_m00A04_phi f)) ∧
    (∃ u : V,
      (∀ v : V, apm_m00A04_phi f u ≤ apm_m00A04_phi f v) ∧
      (∀ v : V, v ≠ u → apm_m00A04_phi f u < apm_m00A04_phi f v) ∧
      ∀ v : V, inner ℝ u v = f v) ∧
    ∀ (n : ℕ) (U : Set (Fin n → ℝ)),
      U.Nonempty → IsOpen U → Bornology.IsBounded U →
      ∀ F : (Fin n → ℝ) → ℝ, apm_m00A04_L2On U F →
        ∃ (u : (Fin n → ℝ) → ℝ)
          (g : Fin n → (Fin n → ℝ) → ℝ),
          apm_m00A04_memH10WithGradient U u g ∧
          ∀ (v : (Fin n → ℝ) → ℝ)
            (h : Fin n → (Fin n → ℝ) → ℝ),
            apm_m00A04_memH10WithGradient U v h →
              (∫ x in U,
                (∑ i : Fin n, g i x * h i x) + u x * v x) =
              ∫ x in U, F x * v x := by
  let u : V := (InnerProductSpace.toDual ℝ V).symm f
  have hu (v : V) : inner ℝ u v = f v := by
    exact InnerProductSpace.toDual_symm_apply
  have hphi (v : V) :
      apm_m00A04_phi f v =
        (1 / 2 : ℝ) * ‖v - u‖ ^ 2 - (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
    unfold apm_m00A04_phi
    rw [← hu v, norm_sub_sq_real, real_inner_comm]
    ring
  constructor
  · refine ⟨-(1 / 2 : ℝ) * ‖u‖ ^ 2, ?_⟩
    rintro _ ⟨v, rfl⟩
    rw [hphi]
    nlinarith [sq_nonneg ‖v - u‖]
  · constructor
    · refine ⟨u, ?_, ?_, hu⟩
      · intro v
        rw [hphi, hphi]
        simp only [sub_self, norm_zero, zero_pow, Nat.ofNat_pos, mul_zero]
        nlinarith [sq_nonneg ‖v - u‖]
      · intro v hv
        rw [hphi, hphi]
        have hnorm : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
        simp only [sub_self, norm_zero, zero_pow, Nat.ofNat_pos, mul_zero]
        nlinarith [sq_pos_of_pos hnorm]
    · intro n U hUne hUopen hUbounded F hF
      by_cases hn : n = 0
      · subst n
        let z : Fin 0 → ℝ := fun i ↦ Fin.elim0 i
        have hsub (x : Fin 0 → ℝ) : x = z := Subsingleton.elim _ _
        have hUtop : U = Set.univ := by
          apply eq_univ_of_forall
          intro x
          obtain ⟨y, hy⟩ := hUne
          simpa [hsub x, hsub y] using hy
        let φ : (Fin 0 → ℝ) → ℝ := fun _ ↦ F z
        have hFφ : F = φ := by
          funext x
          simp only [φ]
          rw [hsub x]
        let g : Fin 0 → (Fin 0 → ℝ) → ℝ := fun i ↦ Fin.elim0 i
        refine ⟨F, g, ?_, ?_⟩
        · refine ⟨hF, ?_, ?_, ?_⟩
          · intro i
            exact Fin.elim0 i
          · intro i
            exact Fin.elim0 i
          · intro ε hε
            refine ⟨φ, ?_, ?_⟩
            · refine ⟨contDiff_const, ?_, ?_⟩
              · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
              · rw [hUtop]
                exact subset_univ _
            · simpa [hFφ] using hε
        · intro v h hv
          simp [hFφ]
      · /-
      Boundary: the Hilbert-space portion is complete above. It uses Mathlib's
      compiled Fréchet–Riesz equivalence `InnerProductSpace.toDual`; rewriting
      `φ` with `norm_sub_sq_real` gives the exact completed-square formula,
      from which boundedness, the unique strict minimizer, and representation
      follow.

      The remaining PDE conjunct is not a direct application of a packaged
      Sobolev/Lax–Milgram theorem because the frozen statement uses the custom
      representative-level predicate `apm_m00A04_memH10WithGradient`. Mathlib
      searches found no `H¹₀` completion matching this predicate. A proof must
      construct the completion of compactly supported smooth test functions in
      the encoded energy norm, prove that its elements admit representatives
      `(u,g)` satisfying the distributional identities and approximation clause,
      then descend the Riesz representative back to those functions. This is a
      full Sobolev-space construction, not supplied by solved siblings.
      Closer hop 1 additionally separates and proves the degenerate case
      `n = 0`: the Euclidean domain is a singleton, the gradient family is
      empty, and a constant test function gives exact energy approximation.
      Thus the sole remaining case has `0 < n` and requires the genuine
      Sobolev completion/representative construction described above.
      Closer hop 2 proves `apm_m00A04_zero_memH10WithGradient`, verifying from
      the frozen definitions that the zero function and zero gradient belong to
      the custom space in every dimension. Searches of
      `Analysis/FunctionalSpaces`, distribution APIs, all closed artifacts,
      `ConstructionTargets`, and `YoungL2.lean` found inequalities and abstract
      Lax--Milgram machinery, but still no completeness/representative theorem
      for this graph closure. Extending the compiled zero base case to arbitrary
      `F` therefore remains exactly the positive-dimensional completion bridge.
      Closer hop 3 proves `apm_m00A04_zero_weak_solution`, closing the full
      variational identity for zero forcing in every dimension. The remaining
      branch is restricted to `0 < n` and `F ≠ 0`. Inspection of
      `Analysis/InnerProductSpace/LaxMilgram.lean` confirms that its theorem
      acts on an already constructed complete Hilbert space; it does not build
      the raw-function/weak-gradient representative space required here.
      -/
        by_cases hF0 : F = 0
        · subst F
          exact apm_m00A04_zero_weak_solution U
        · /-
          Remaining boundary: construct the energy completion of compactly
          supported smooth tests and prove its elements admit representatives
          satisfying `apm_m00A04_memH10WithGradient`.
          -/
          exact apm_m00A04_positive_dimensional_weak_solution
            hn U hUne hUopen hUbounded F hF hF0
