import Mathlib

/-!
# APM t01A08

## Statement repairs

The codomain written once as `A` and later as `𝐀³` is read consistently as
real affine three-space `ℝ³`.

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
    [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I (⊤ : ℕ∞) X]
    (f : X → apm_t01a08_R3)
    (hf : ContMDiff I apm_t01a08_I3 (⊤ : ℕ∞) f) :
    ∃ p : apm_t01a08_R2,
      (∀ x : X,
        f x ∈ apm_t01a08_line p →
          Function.Surjective
            (mfderiv I apm_t01a08_I2
              (fun z => apm_t01a08_projection (f z)) x)) := by
  /-
  Boundary (skipped): the intended route is Sard's theorem for
  `projection ∘ f`, but Mathlib does not currently provide manifold Sard in
  this generality. More importantly, the frozen statement omits a
  second-countability (or comparable countability) hypothesis on `X`, so it
  is false as stated: take an uncountable topological sum of positive-
  dimensional manifold components indexed by `p : R²`, and map the entire
  `p`-component constantly to a point of `R³` whose projection is `p`. The map
  is smooth and its projection is surjective, but its derivative is zero on
  every fiber, hence no `p` is a regular value. I searched the manifold
  regular-value, critical-value, Sard, and Whitney-embedding APIs; the only
  Sard-related code assumes additional countability/local-Lipschitz machinery
  and does not supply this theorem. Mathlib's own `IsManifold` documentation
  explicitly says that neither Hausdorffness nor second countability is part
  of the class. The partial sibling `t92J07` adds both hypotheses for the
  corresponding countable-family Sard claim, while `t01J04` records another
  failure caused by the deliberately weak manifold axioms. No relevant bridge
  occurs in `ConstructionTargets/` or `YoungL2.lean`.
  -/
  sorry
