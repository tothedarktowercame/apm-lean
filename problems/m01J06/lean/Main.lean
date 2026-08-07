import Mathlib

/-!
# APM m01J06: Loaded-rod extremals and buckling loads

## Statement repairs

The phrase "Based no these results" is read as "Based on these results". No
mathematical repair is made.

## Encoding questions

The source's final request asks whether nontrivial solutions are "expected".
We encode that qualitative conclusion as the standard precise bifurcation
statement: nonzero nonlinear solutions occur arbitrarily close to each
linearized critical load and arbitrarily close to the zero configuration.
-/

open MeasureTheory Set

noncomputable section

def apm_m01J06_energy (lam K : ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∫ s in Icc (0 : ℝ) 1,
    lam * Real.cos (φ s) + (1 / 2 : ℝ) * K * (derivWithin φ (Icc 0 1) s) ^ 2

def apm_m01J06_admissible (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Icc 0 1) ∧ φ 0 = 0

def apm_m01J06_stationary (lam K : ℝ) (φ : ℝ → ℝ) : Prop :=
  apm_m01J06_admissible φ ∧
  ∀ η : ℝ → ℝ, ContDiffOn ℝ 2 η (Icc 0 1) → η 0 = 0 →
    DifferentiableAt ℝ
      (fun ε : ℝ ↦ apm_m01J06_energy lam K (fun s ↦ φ s + ε * η s)) 0 ∧
    deriv (fun ε : ℝ ↦
      apm_m01J06_energy lam K (fun s ↦ φ s + ε * η s)) 0 = 0

def apm_m01J06_nonlinearSolution (lam K : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Icc 0 1) ∧
  φ 0 = 0 ∧ derivWithin φ (Icc 0 1) 1 = 0 ∧
  ∀ s ∈ Ioo (0 : ℝ) 1,
    K * iteratedDerivWithin 2 φ (Icc 0 1) s +
      lam * Real.sin (φ s) = 0

def apm_m01J06_linearMode (lam K : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Icc 0 1) ∧
  φ 0 = 0 ∧ derivWithin φ (Icc 0 1) 1 = 0 ∧
  ∀ s ∈ Ioo (0 : ℝ) 1,
    K * iteratedDerivWithin 2 φ (Icc 0 1) s + lam * φ s = 0

def apm_m01J06_nontrivial (φ : ℝ → ℝ) : Prop :=
  ∃ s ∈ Icc (0 : ℝ) 1, φ s ≠ 0

def apm_m01J06_criticalLoad (K : ℝ) (m : ℕ) : ℝ :=
  K * (((2 * (m : ℝ) + 1) * Real.pi / 2) ^ 2)

def apm_m01J06_isBifurcationLoad (K lamStar : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ lam : ℝ, ∃ φ : ℝ → ℝ,
      0 < lam ∧ |lam - lamStar| < δ ∧
      apm_m01J06_nonlinearSolution lam K φ ∧
      apm_m01J06_nontrivial φ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, |φ s| < δ

private lemma apm_m01J06_mode_hasDerivAt (w s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.sin (w * t))
      (w * Real.cos (w * s)) s := by
  convert (Real.hasDerivAt_sin (w * s)).comp s
    (hasDerivAt_const s w |>.mul (hasDerivAt_id s)) using 1 <;> ring

private lemma apm_m01J06_mode_hasSecondDerivAt (w s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ w * Real.cos (w * t))
      (-(w ^ 2) * Real.sin (w * s)) s := by
  convert (hasDerivAt_const s w).mul
    ((Real.hasDerivAt_cos (w * s)).comp s
      (hasDerivAt_const s w |>.mul (hasDerivAt_id s))) using 1 <;> ring

private lemma apm_m01J06_mode_iteratedDerivWithin_two
    (w s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin 2 (fun t : ℝ ↦ Real.sin (w * t)) (Icc 0 1) s =
      -(w ^ 2) * Real.sin (w * s) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
    (by fun_prop) hs]
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one]
  have hfirst : deriv (fun t : ℝ ↦ Real.sin (w * t)) =
      fun t ↦ w * Real.cos (w * t) := by
    funext t
    exact (apm_m01J06_mode_hasDerivAt w t).deriv
  rw [hfirst]
  exact (apm_m01J06_mode_hasSecondDerivAt w s).deriv

private lemma apm_m01J06_critical_mode_exists (K : ℝ) (m : ℕ) :
    ∃ φ : ℝ → ℝ,
      apm_m01J06_linearMode (apm_m01J06_criticalLoad K m) K φ ∧
        apm_m01J06_nontrivial φ := by
  let w : ℝ := (2 * (m : ℝ) + 1) * Real.pi / 2
  refine ⟨fun s ↦ Real.sin (w * s), ?_, ?_⟩
  · refine ⟨by fun_prop, by simp, ?_, ?_⟩
    · have hd := (apm_m01J06_mode_hasDerivAt w 1).hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt (by simp))
      rw [hd]
      have hw : w = Real.pi / 2 + m * Real.pi := by
        dsimp [w]
        push_cast
        ring
      rw [hw, mul_one, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero, mul_zero]
    · intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
      rw [apm_m01J06_mode_iteratedDerivWithin_two w s hs']
      unfold apm_m01J06_criticalLoad
      dsimp [w]
      ring
  · refine ⟨1, by simp, ?_⟩
    have hw : w = Real.pi / 2 + m * Real.pi := by
      dsimp [w]
      push_cast
      ring
    change Real.sin (w * 1) ≠ 0
    rw [mul_one, hw, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
    exact mul_ne_zero (pow_ne_zero m (by norm_num : (-1 : ℝ) ≠ 0)) one_ne_zero

theorem apm_m01j06
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    (∀ φ : ℝ → ℝ,
      apm_m01J06_stationary lam K φ →
        apm_m01J06_nonlinearSolution lam K φ) ∧
    apm_m01J06_stationary lam K (fun _ ↦ 0) ∧
    ((∃ φ : ℝ → ℝ,
        apm_m01J06_linearMode lam K φ ∧ apm_m01J06_nontrivial φ) ↔
      ∃ m : ℕ, lam = apm_m01J06_criticalLoad K m) ∧
    (∀ m : ℕ,
      apm_m01J06_isBifurcationLoad K (apm_m01J06_criticalLoad K m)) := by
  constructor
  · /-
    Boundary (closer hop 2) for Euler–Lagrange: expand the derivative of
    `apm_m01J06_energy` under the interval integral, integrate the
    `derivWithin φ * derivWithin η` term by parts, then apply the
    fundamental lemma first to variations vanishing at both endpoints and
    finally to a variation free at `1`. Searches covered
    `intervalIntegral.integral_mul_deriv_eq_deriv_mul`, its
    `AbsolutelyContinuousOnInterval` variant, the set-integral/interval-
    integral conversion, and differentiation under an integral.  The
    integration-by-parts theorem is usable once the first variation is known,
    but no searched theorem derives that first variation for this `Icc`
    set-integral from only `ContDiffOn`; uniform domination in `ε` and the
    conversion between the resulting derivatives and `derivWithin` remain.
    -/
    sorry
  · constructor
    · have hzero_admissible : apm_m01J06_admissible (fun _ : ℝ ↦ 0) := by
        constructor
        · fun_prop
        · rfl
      refine ⟨hzero_admissible, ?_⟩
      /-
      Boundary (closer hop 2) for stationarity of zero: for each admissible `η`, the energy
      along `ε ↦ εη` has derivative zero at zero because the cosine term
      differentiates to `-lam * sin 0 * η` and the bending term is quadratic
      in `ε`. The remaining API work is the same differentiation-under-the-
      integral and `derivWithin` scalar-linearity bridge as in the first
      conjunct.  Recasting the energy as an even function of `ε` proves only
      that any existing derivative is zero; the frozen predicate separately
      requires `DifferentiableAt`, so evenness does not route around the
      missing differentiation-under-the-set-integral proof.
      -/
      sorry
    · constructor
      · constructor
        · intro hmode
          /-
          Boundary (closer hop 2) for the linear spectrum, converse only:
          `apm_m01J06_critical_mode_exists` now proves the complete forward
          construction for every `m`, including `ContDiffOn`, both mixed
          boundary conditions, the `iteratedDerivWithin 2` equation, and
          nontriviality.  What remains here is to classify an arbitrary
          nontrivial `ContDiffOn ℝ 2` solution of
          `K φ'' + lam φ = 0`, `φ 0 = 0`, `φ' 1 = 0`.

          Searches of Mathlib's ODE uniqueness, `ContDiffOn`, within-derivative,
          and Sturm--Liouville APIs found no theorem converting this custom
          within-derivative solution into `A*sin (sqrt(lam/K)*s)`.  The local
          route requires proving constancy of the Wronskian/energy on `Icc`,
          obtaining the sine normal form, then applying `Real.cos_eq_zero_iff`
          and positivity to extract the natural-number frequency index.
          -/
          sorry
        · rintro ⟨m, rfl⟩
          exact apm_m01J06_critical_mode_exists K m

      · intro m
        have hfrequency :
            0 < ((2 * (m : ℝ) + 1) * Real.pi / 2) := by positivity
        have hcritical : 0 < apm_m01J06_criticalLoad K m := by
          unfold apm_m01J06_criticalLoad
          positivity
        /-
        Boundary (closer hop 2) for nonlinear bifurcation: positivity of the frequency and
        critical load is compiled above. The remaining conclusion is a genuine
        local bifurcation theorem (construct nonzero pendulum solutions with
        both load and sup-amplitude arbitrarily close to the critical pair).
        Repository and Mathlib searches found no Crandall–Rabinowitz,
        Lyapunov–Schmidt, implicit-function shooting, or pendulum-period theorem
        reusable for this custom BVP.  The now-compiled exact linear critical
        modes establish the kernel direction but do not supply the nonlinear
        solution branch required by the quantified frozen predicate.
        -/
        sorry
