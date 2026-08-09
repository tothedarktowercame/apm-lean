import Mathlib

/-!
# APM t01A08

## Statement repairs

1. The codomain written once as `A` and later as `𝐀³` is read consistently as
   real affine three-space `ℝ³`.
2. The usual second-countability convention implicit in the source's “smooth
   manifold” is made explicit. Mathlib's `IsManifold` deliberately omits it;
   without this hypothesis an uncountable disjoint union of components can
   make every value critical while the projection remains surjective.

## Encoding questions

Mathlib does not yet expose a general embedded-submanifold predicate. The claim
that the inverse image is smooth is encoded by the equivalent regular-value
criterion for a projection `ℝ³ → ℝ²`; its fibers are literal affine lines.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t01a08_R2 := Fin 2 → ℝ
abbrev apm_t01a08_R3 := Fin 3 → ℝ
abbrev apm_t01a08_I2 := 𝓘(ℝ, apm_t01a08_R2)
abbrev apm_t01a08_I3 := 𝓘(ℝ, apm_t01a08_R3)

def apm_t01a08_projection (x : apm_t01a08_R3) : apm_t01a08_R2 :=
  fun i : Fin 2 => x i.castSucc

def apm_t01a08_line (p : apm_t01a08_R2) : Set apm_t01a08_R3 :=
  {x | apm_t01a08_projection x = p}

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
  sorry
