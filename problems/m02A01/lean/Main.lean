import Mathlib

/-!
# APM m02A01: Weak and strong convergence

## Statement repairs

None.

## Encoding questions

None. Weak convergence uses Mathlib's genuine weak topology, and the strict
counterexample is the standard unit-vector sequence in the actual Banach space
`ℓ²(ℕ, ℝ)`.
-/

open Filter

noncomputable section

def apm_m02A01_weaklyConverges {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (x : ℕ → X) (a : X) : Prop :=
  Tendsto (fun n ↦ toWeakSpace ℝ X (x n)) atTop
    (nhds (toWeakSpace ℝ X a))

abbrev apm_m02A01_l2 := lp (fun _ : ℕ ↦ ℝ) 2

def apm_m02A01_basisVector (n : ℕ) : apm_m02A01_l2 :=
  lp.single 2 n 1

theorem apm_m02a01 :
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (x : ℕ → X) (a b : X),
      apm_m02A01_weaklyConverges x a →
      apm_m02A01_weaklyConverges x b → a = b) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        (x : ℕ → X) (a : X),
      Tendsto x atTop (nhds a) → apm_m02A01_weaklyConverges x a) ∧
    (apm_m02A01_weaklyConverges apm_m02A01_basisVector 0 ∧
      ¬Tendsto apm_m02A01_basisVector atTop (nhds 0)) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
        [FiniteDimensional ℝ X] (x : ℕ → X) (a : X),
      apm_m02A01_weaklyConverges x a ↔ Tendsto x atTop (nhds a)) := by
  constructor
  · intro X _ _ x a b ha hb
    exact (toWeakSpace ℝ X).injective (tendsto_nhds_unique ha hb)
  · constructor
    · intro X _ _ x a hx
      exact (toWeakSpaceCLM ℝ X).continuous.continuousAt.tendsto.comp hx
    · constructor
      · constructor
        · /-
          Boundary for weak convergence of the `ℓ²` basis: unfold weak-space
          convergence using `tendsto_iff_forall_eval_tendsto_topDualPairing`,
          represent each continuous functional by its Riesz vector, and show
          its coordinates tend to zero. Searches found the weak-topology
          evaluation criterion and `lp.single`, but no packaged Riesz
          representation theorem specialized to `lp` or lemma that coordinates
          of an `ℓ²` vector tend to zero.
          -/
          sorry
        · intro hstrong
          have hnorm : Tendsto (fun n ↦ ‖apm_m02A01_basisVector n‖) atTop
              (nhds ‖(0 : apm_m02A01_l2)‖) :=
            continuous_norm.continuousAt.tendsto.comp hstrong
          have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 0) := by
            simpa [apm_m02A01_basisVector, lp.norm_single] using hnorm
          have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hone
          norm_num at this
      · intro X _ _ _ x a
        constructor
        · /-
          Boundary for finite-dimensional weak-to-strong convergence: Mathlib
          records that the weak topology is coarser via `toWeakSpaceCLM`, but
          `Topology/Algebra/Module/WeakDual.lean` explicitly lists equality of
          weak and norm topologies in finite dimension as TODO. A local proof
          requires choosing a finite basis, proving its coordinate functionals
          continuous, and assembling coordinatewise convergence into norm
          convergence.
          -/
          sorry
        · intro hx
          exact (toWeakSpaceCLM ℝ X).continuous.continuousAt.tendsto.comp hx
