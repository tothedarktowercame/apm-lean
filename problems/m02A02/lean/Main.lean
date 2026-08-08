import Mathlib

/-!
# APM m02A02 — the periodic Poisson problem in a Fourier Sobolev model

The periodic Sobolev space is constructed concretely as weighted Fourier
`ℓ²(ℤ², ℂ)`, following the one-dimensional construction in `m95A02`.  An
element stores its Fourier coefficient in the normalized basis whose `ℓ²`
inner product is the `H¹` inner product.  Conjugate symmetry cuts out the
real-valued functions, rapid decay represents smooth periodic functions, and
the zero Fourier mode is the mean.

## Statement repairs

The periodic Poisson equation requires the standard compatibility condition
that the forcing have zero mean; this omitted hypothesis is added explicitly.

## Encoding questions

None.
-/

open Filter Set

noncomputable section

abbrev M02A02Freq := ℤ × ℤ
abbrev M02A02H1 := lp (fun _ : M02A02Freq => ℂ) 2
abbrev M02A02L2 := lp (fun _ : M02A02Freq => ℂ) 2

def m02A02FreqSq (k : M02A02Freq) : ℝ :=
  (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2

def m02A02Weight (k : M02A02Freq) : ℝ :=
  1 + 4 * Real.pi ^ 2 * m02A02FreqSq k

/-- The physical Fourier coefficient represented by a normalized `H¹`
coefficient vector. -/
def m02A02Coeff (u : M02A02H1) (k : M02A02Freq) : ℂ :=
  u k / (Real.sqrt (m02A02Weight k) : ℂ)

/-- Conjugate symmetry characterizes Fourier coefficients of real functions. -/
def m02A02IsReal (u : M02A02H1) : Prop :=
  ∀ k : M02A02Freq, u (-k.1, -k.2) = star (u k)

/-- Rapid decay of physical coefficients is the Fourier characterization of
a smooth periodic function. -/
def m02A02IsSmoothPeriodic (u : M02A02H1) : Prop :=
  m02A02IsReal u ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ k : M02A02Freq,
      ‖m02A02Coeff u k‖ * (1 + m02A02FreqSq k) ^ N ≤ C

def m02A02IsMeanZero (u : M02A02H1) : Prop :=
  m02A02IsReal u ∧ u (0, 0) = 0

abbrev M02A02RealH1 := {u : M02A02H1 // m02A02IsReal u}
def m02A02SmoothPeriodicH1 : Set M02A02RealH1 :=
  {u | m02A02IsSmoothPeriodic u.1}

/-- The real, mean-zero Fourier vectors form the concrete real vector space
`H¹_{P,0}`. -/
def m02A02MeanZeroH1 : Submodule ℝ M02A02H1 where
  carrier := {u | m02A02IsMeanZero u}
  zero_mem' := by
    constructor
    · intro k
      have hz : ⇑(0 : M02A02H1) = (0 : M02A02Freq → ℂ) :=
        lp.coeFn_zero _ _
      rw [congrFun hz (-k.1, -k.2), congrFun hz k]
      simp
    · have hz : ⇑(0 : M02A02H1) = (0 : M02A02Freq → ℂ) :=
        lp.coeFn_zero _ _
      rw [congrFun hz (0, 0)]
      simp
  add_mem' := by
    intro u v hu hv
    have hadd : ⇑(u + v) = ⇑u + ⇑v := lp.coeFn_add u v
    constructor
    · intro k
      rw [congrFun hadd (-k.1, -k.2), congrFun hadd k]
      simp only [Pi.add_apply]
      rw [hu.1 k, hv.1 k]
      exact (map_add (starRingEnd ℂ) (u k) (v k)).symm
    · rw [congrFun hadd (0, 0), Pi.add_apply, hu.2, hv.2, add_zero]
  smul_mem' := by
    intro c u hu
    have hsmul : ⇑(c • u) = c • ⇑u := lp.coeFn_smul c u
    constructor
    · intro k
      rw [congrFun hsmul (-k.1, -k.2), congrFun hsmul k]
      simp only [Pi.smul_apply]
      rw [hu.1 k]
      simp [smul_eq_mul]
    · rw [congrFun hsmul (0, 0), Pi.smul_apply, hu.2]
      exact smul_zero c

/-- The `L²` inner product, recovered from normalized `H¹` coefficients. -/
def m02A02L2Pair (u v : M02A02H1) : ℝ :=
  ∑' k : M02A02Freq,
    (star (m02A02Coeff u k) * m02A02Coeff v k).re

/-- Dirichlet form `∫ ∇u · ∇v`, expressed by Fourier multipliers. -/
def m02A02DirichletPair (u v : M02A02H1) : ℝ :=
  ∑' k : M02A02Freq,
    4 * Real.pi ^ 2 * m02A02FreqSq k *
      (star (m02A02Coeff u k) * m02A02Coeff v k).re

def m02A02GradientEnergy (u : M02A02H1) : ℝ :=
  m02A02DirichletPair u u

def m02A02L2Energy (u : M02A02H1) : ℝ :=
  m02A02L2Pair u u

/-- Pairing an `L²` forcing, represented by its ordinary Fourier
coefficients, with a periodic Sobolev test function. -/
def m02A02ForcingPair (f : M02A02L2) (v : M02A02H1) : ℝ :=
  ∑' k : M02A02Freq,
    (star (f k) * m02A02Coeff v k).re

def m02A02WeakSolution (u : M02A02H1) (f : M02A02L2) : Prop :=
  ∀ v : M02A02H1, m02A02IsMeanZero v →
    m02A02DirichletPair u v = m02A02ForcingPair f v

/-- Fourier-coefficient form of `-Δu = f`. -/
def m02A02HasPoissonEquation (u : M02A02H1) (f : M02A02L2) : Prop :=
  ∀ k : M02A02Freq,
    (4 * Real.pi ^ 2 * m02A02FreqSq k : ℂ) * m02A02Coeff u k = f k

theorem apm_m02a02 :
    Dense m02A02SmoothPeriodicH1 ∧
    IsClosed (m02A02MeanZeroH1 : Set M02A02H1) ∧
    Nonempty (CompleteSpace (↥m02A02MeanZeroH1)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ u : M02A02H1,
      m02A02IsMeanZero u →
      m02A02L2Energy u ≤ C * m02A02GradientEnergy u) ∧
    ∀ (u₀ : M02A02H1) (f : M02A02L2),
      m02A02IsReal u₀ →
      (∀ k : M02A02Freq, f (-k.1, -k.2) = star (f k)) →
      f (0, 0) = 0 →
      (∃! u : M02A02H1,
        m02A02IsReal u ∧ m02A02IsMeanZero (u - u₀) ∧
          m02A02WeakSolution u f) ∧
      (∀ u : M02A02H1,
        m02A02IsReal u → m02A02IsMeanZero (u - u₀) →
        (m02A02WeakSolution u f ↔ m02A02HasPoissonEquation u f)) := by
  sorry
