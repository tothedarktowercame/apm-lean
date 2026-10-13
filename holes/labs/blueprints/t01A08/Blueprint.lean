import ConstructionTargets.SardConvexDomain

/-!
# Blueprint for APM t01A08

The sole library obligation is Sard's theorem for the projected map on an
arbitrary finite-dimensional manifold with corners.  The consumer-side
selection and identification of a projection fiber with a line are explicit.
-/

open scoped ContDiff Manifold
open MeasureTheory

noncomputable section

abbrev apm_t01a08_R2 := Fin 2 → ℝ
abbrev apm_t01a08_R3 := Fin 3 → ℝ
abbrev apm_t01a08_I2 := 𝓘(ℝ, apm_t01a08_R2)
abbrev apm_t01a08_I3 := 𝓘(ℝ, apm_t01a08_R3)

def apm_t01a08_projection (x : apm_t01a08_R3) : apm_t01a08_R2 :=
  fun i : Fin 2 => x i.castSucc

def apm_t01a08_line (p : apm_t01a08_R2) : Set apm_t01a08_R3 :=
  {x | apm_t01a08_projection x = p}

/-- LIBRARY (Morse--Sard for finite-dimensional manifolds with corners):
almost every point of the coordinate plane is a regular value of the
projection of `f`. -/
theorem apm_t01a08_ae_regularValue_projection
    (E H X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [TopologicalSpace X] [SecondCountableTopology X] [ChartedSpace H X]
    [IsManifold I (⊤ : ℕ∞) X]
    (f : X → apm_t01a08_R3)
    (hf : ContMDiff I apm_t01a08_I3 (⊤ : ℕ∞) f) :
    ∀ᵐ p : apm_t01a08_R2,
      ∀ x : X, apm_t01a08_projection (f x) = p →
        Function.Surjective
          (mfderiv I apm_t01a08_I2
            (fun z => apm_t01a08_projection (f z)) x) := by
  sorry

/-- An almost-everywhere regular-value statement supplies one regular value. -/
theorem apm_t01a08_exists_regularValue_of_ae
    (P : apm_t01a08_R2 → Prop)
    (hP : ∀ᵐ p : apm_t01a08_R2, P p) : ∃ p, P p := by
  exact hP.exists

theorem apm_t01a08
    (E H X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [TopologicalSpace X] [SecondCountableTopology X] [ChartedSpace H X]
    [IsManifold I (⊤ : ℕ∞) X]
    (f : X → apm_t01a08_R3)
    (hf : ContMDiff I apm_t01a08_I3 (⊤ : ℕ∞) f) :
    ∃ p : apm_t01a08_R2,
      (∀ x : X,
        f x ∈ apm_t01a08_line p →
          Function.Surjective
            (mfderiv I apm_t01a08_I2
              (fun z => apm_t01a08_projection (f z)) x)) := by
  apply apm_t01a08_exists_regularValue_of_ae
  filter_upwards [apm_t01a08_ae_regularValue_projection E H X I f hf] with p hp
  simpa [apm_t01a08_line] using hp

#print axioms apm_t01a08
