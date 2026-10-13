import Mathlib

/-!
# APM m98J02

## Statement repairs

Part (d) assumes only `f ∈ C²(ℝ²)`, but the convolution construction in
parts (b)--(c) requires one factor to have compact support. Following the
informal solution, `f` is minimally assumed compactly supported. This is also
the hypothesis under which the convolution is defined here.  The printed
regularity conclusion is false for an arbitrary fundamental distribution of
this non-hypoelliptic operator.  Following the informal solution's explicit
function-level convolution argument, `w₀` is additionally required to be the
regular distribution represented by a locally integrable function.

The garbled operator typography is read, as in the supplied solution, as
`T = 2 ∂²/∂x² - ∂/∂y + 3 ∂²/(∂x∂y)`.

The former first conjunct merely unfolded `apm_m98J02_hasCompactSupport`.
Since the definition above already supplies part (a), that tautology is
replaced by the substantive closure of compactly supported distributions
under addition.

Revised 2026-10-13: in `apm_m98J02_isConvolution` the cutoff `χ` must equal one
on an open neighbourhood of `K`, not merely at the points of `K`. With the pointwise
condition, a distribution of positive order (for example `δ₀'`, with `K = {0}`) sees
the derivatives of `χ` at `K`, so the defining pairing depended on the cutoff and
the definition did not determine the convolution (found by a lemma seat, round 2).

## Encoding questions

Mathlib currently provides `Distribution` but not the general convolution of
a compactly supported distribution with an arbitrary distribution, nor
general distributional partial derivatives. Consequently these are encoded
by their defining test-function identities. `apm_m98J02_isConvolution` uses a
test-function cutoff equal to one on a compact support of the first factor;
`apm_m98J02_solvesT` uses the formal adjoint
`2∂ₓ² + ∂ᵧ + 3∂ₓ∂ᵧ` on test functions. No function-level surrogate
replaces the distributions.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

noncomputable section

abbrev apm_m98J02_E := EuclideanSpace ℝ (Fin 2)

abbrev apm_m98J02_Test :=
  TestFunction (⊤ : Opens apm_m98J02_E) ℝ ⊤

abbrev apm_m98J02_Dist :=
  Distribution (⊤ : Opens apm_m98J02_E) ℝ ⊤

/-- A distribution vanishes on every test function supported off one compact set. -/
def apm_m98J02_hasCompactSupport (u : apm_m98J02_Dist) : Prop :=
  ∃ K : Set apm_m98J02_E, IsCompact K ∧
    ∀ φ : apm_m98J02_Test, Disjoint (tsupport (φ : apm_m98J02_E → ℝ)) K → u φ = 0

/-- The defining pairing for convolution when the first factor has compact support.

The cutoff `χ` lets the compactly supported distribution `u` act on the
generally non-compact smooth function `x ↦ v (y ↦ φ (x + y))`. -/
def apm_m98J02_isConvolution
    (u v w : apm_m98J02_Dist) : Prop :=
  ∀ φ : apm_m98J02_Test,
    ∃ (K : Set apm_m98J02_E) (χ Ψ : apm_m98J02_Test),
      IsCompact K ∧
      (∀ η : apm_m98J02_Test,
        Disjoint (tsupport (η : apm_m98J02_E → ℝ)) K → u η = 0) ∧
      (∃ U : Set apm_m98J02_E, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, χ x = 1) ∧
      (∀ x : apm_m98J02_E,
        ∃ τ : apm_m98J02_Test,
          (∀ y : apm_m98J02_E, τ y = φ (x + y)) ∧ Ψ x = χ x * v τ) ∧
      w φ = u Ψ

/-- Directional partial derivative in one of the two coordinate directions. -/
def apm_m98J02_partial (i : Fin 2) (f : apm_m98J02_E → ℝ)
    (x : apm_m98J02_E) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The formal adjoint of `2∂ₓ² - ∂ᵧ + 3∂ₓ∂ᵧ`. -/
def apm_m98J02_formalAdjoint (f : apm_m98J02_E → ℝ)
    (x : apm_m98J02_E) : ℝ :=
  2 * apm_m98J02_partial 0 (apm_m98J02_partial 0 f) x +
    apm_m98J02_partial 1 f x +
    3 * apm_m98J02_partial 0 (apm_m98J02_partial 1 f) x

/-- Distributional equation `T w = r`, expressed against test functions. -/
def apm_m98J02_solvesT
    (w : apm_m98J02_Dist) (r : apm_m98J02_Test → ℝ) : Prop :=
  ∀ φ : apm_m98J02_Test,
    ∃ ψ : apm_m98J02_Test,
      (∀ x : apm_m98J02_E,
        ψ x = apm_m98J02_formalAdjoint (φ : apm_m98J02_E → ℝ) x) ∧
      w ψ = r φ

/-- A distribution is the regular distribution induced by a function. -/
def apm_m98J02_representsFunction
    (u : apm_m98J02_Dist) (f : apm_m98J02_E → ℝ) : Prop :=
  ∀ φ : apm_m98J02_Test, u φ = ∫ x, f x * φ x

/-- Compactly supported distributions are closed under addition directly from
the support definition. -/
lemma apm_m98J02_hasCompactSupport_add
    (u v : apm_m98J02_Dist)
    (hu : apm_m98J02_hasCompactSupport u)
    (hv : apm_m98J02_hasCompactSupport v) :
    apm_m98J02_hasCompactSupport (u + v) := by
  obtain ⟨Ku, hKuc, hKu⟩ := hu
  obtain ⟨Kv, hKvc, hKv⟩ := hv
  refine ⟨Ku ∪ Kv, hKuc.union hKvc, ?_⟩
  intro φ hdis
  have hd := disjoint_union_right.mp hdis
  simp [hKu φ hd.1, hKv φ hd.2]

@[simp] lemma apm_m98J02_hasCompactSupport_zero :
    apm_m98J02_hasCompactSupport (0 : apm_m98J02_Dist) := by
  refine ⟨∅, isCompact_empty, ?_⟩
  simp

lemma apm_m98J02_hasCompactSupport_neg
    (u : apm_m98J02_Dist) (hu : apm_m98J02_hasCompactSupport u) :
    apm_m98J02_hasCompactSupport (-u) := by
  obtain ⟨K, hKc, hK⟩ := hu
  refine ⟨K, hKc, ?_⟩
  intro φ hdis
  simp [hK φ hdis]

lemma apm_m98J02_hasCompactSupport_sub
    (u v : apm_m98J02_Dist)
    (hu : apm_m98J02_hasCompactSupport u)
    (hv : apm_m98J02_hasCompactSupport v) :
    apm_m98J02_hasCompactSupport (u - v) := by
  rw [sub_eq_add_neg]
  exact apm_m98J02_hasCompactSupport_add u (-v) hu
    (apm_m98J02_hasCompactSupport_neg v hv)

lemma apm_m98J02_hasCompactSupport_smul
    (c : ℝ) (u : apm_m98J02_Dist)
    (hu : apm_m98J02_hasCompactSupport u) :
    apm_m98J02_hasCompactSupport (c • u) := by
  obtain ⟨K, hKc, hK⟩ := hu
  refine ⟨K, hKc, ?_⟩
  intro φ hdis
  simp [hK φ hdis]

/-- Adding a homogeneous solution preserves the encoded inhomogeneous
distributional equation. -/
lemma apm_m98J02_solvesT_add_homogeneous
    (w z : apm_m98J02_Dist) (r : apm_m98J02_Test → ℝ)
    (hw : apm_m98J02_solvesT w r)
    (hz : apm_m98J02_solvesT z (fun _ ↦ 0)) :
    apm_m98J02_solvesT (w + z) r := by
  intro φ
  obtain ⟨ψ, hψ, hwψ⟩ := hw φ
  obtain ⟨η, hη, hzη⟩ := hz φ
  have hηψ : η = ψ := by
    ext x
    rw [hη x, hψ x]
  subst η
  refine ⟨ψ, hψ, ?_⟩
  simp [hwψ, hzη]

/-- Translation of a test function by a fixed vector.  This is the test
function required pointwise in the definition of distributional convolution. -/
def apm_m98J02_translateTest (x : apm_m98J02_E)
    (φ : apm_m98J02_Test) : apm_m98J02_Test where
  toFun := fun y ↦ φ (x + y)
  contDiff' := φ.contDiff.comp (contDiff_const.add contDiff_id)
  hasCompactSupport' :=
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft x)
  tsupport_subset' := by simp

@[simp] lemma apm_m98J02_translateTest_apply
    (x y : apm_m98J02_E) (φ : apm_m98J02_Test) :
    apm_m98J02_translateTest x φ y = φ (x + y) := rfl

/-- Why this unblocks the cutoff step in `apm_m98j02`: every compact subset
of the Euclidean plane admits a compactly supported smooth function that is
identically one on that subset. -/
theorem apm_m98J02_bridge_1
    (K : Set apm_m98J02_E) (hK : IsCompact K) :
    ∃ χ : apm_m98J02_Test, ∃ U : Set apm_m98J02_E, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, χ x = 1 := by
  sorry

/-- Why this unblocks the convolution step in `apm_m98j02`: this packages the
iterated pairing
`φ ↦ u (x ↦ χ x * v (y ↦ φ (x + y)))` as a continuous linear functional on
the LF space of test functions.  The conclusion records all cutoff and
translation identities needed by the concrete convolution definition. -/
theorem apm_m98J02_bridge_2
    (u v : apm_m98J02_Dist) (K : Set apm_m98J02_E)
    (hK : IsCompact K)
    (huK : ∀ η : apm_m98J02_Test,
      Disjoint (tsupport (η : apm_m98J02_E → ℝ)) K → u η = 0) :
    ∃ w : apm_m98J02_Dist, apm_m98J02_isConvolution u v w := by
  sorry

theorem apm_m98j02 :
    (∀ u v : apm_m98J02_Dist,
      apm_m98J02_hasCompactSupport u →
      apm_m98J02_hasCompactSupport v →
      apm_m98J02_hasCompactSupport (u + v)) ∧
    (∀ u v : apm_m98J02_Dist,
      apm_m98J02_hasCompactSupport u →
        ∃ w : apm_m98J02_Dist, apm_m98J02_isConvolution u v w) ∧
    ∀ (f k : apm_m98J02_E → ℝ) (w₀ : apm_m98J02_Dist),
      ContDiff ℝ 2 f → IsCompact (tsupport f) →
      LocallyIntegrable k → apm_m98J02_representsFunction w₀ k →
      apm_m98J02_solvesT w₀ (fun φ ↦ φ 0) →
      ∃ (u w w' : apm_m98J02_Dist) (g : apm_m98J02_E → ℝ),
        apm_m98J02_representsFunction u f ∧
        apm_m98J02_hasCompactSupport u ∧
        apm_m98J02_isConvolution u w₀ w ∧
        apm_m98J02_representsFunction w g ∧
        ContDiff ℝ 2 g ∧
        apm_m98J02_solvesT w (fun φ ↦ ∫ x, f x * φ x) ∧
        w' ≠ w ∧
        apm_m98J02_solvesT w' (fun φ ↦ ∫ x, f x * φ x) := by
  refine ⟨?_, ?_⟩
  · intro u v hu hv
    exact apm_m98J02_hasCompactSupport_add u v hu hv
  · /-
    CLOSER HOP 3 boundary. The first conjunct is fully proved above as
    `apm_m98J02_hasCompactSupport_add`, using the union of two compact support
    witnesses and `disjoint_union_right`.

    This hop extends the compiled support calculus with closure under zero,
    negation, subtraction, and real scalar multiplication. It also proves
    `apm_m98J02_solvesT_add_homogeneous`: adding a homogeneous solution to an
    inhomogeneous one preserves the encoded equation. Thus the algebraic part
    of nonuniqueness is complete; only a nonzero homogeneous witness is absent.

    I searched `LEMMA-INDEX.md`, all 16 `ConstructionTargets/` modules, the
    closed distribution artifacts, Mathlib's `Distribution`, `TestFunction`,
    `SchwartzMap`, bump-function, and tempered-distribution sources, and git
    history. Mathlib has `SchwartzMap.integralCLM` and constructors of regular
    tempered distributions, but no continuous-linear constructor into this
    `Distribution (⊤ : Opens E) ℝ ⊤` type for
    `φ ↦ ∫ x, f x * φ x`. Thus even the canonical regular distribution `u`
    requires a new continuity proof for the test-function LF topology.

    Going beyond hop 2, `apm_m98J02_translateTest` now constructs, for every
    `x` and `φ`, the required translated test function `y ↦ φ (x+y)`.
    Its smoothness follows by composition and compact support follows from
    `HasCompactSupport.comp_homeomorph` with `Homeomorph.addLeft`; the exact
    evaluation equation is compiled as `apm_m98J02_translateTest_apply`.

    The second conjunct still requires a cutoff test function equal to one on
    the compact support, followed by continuity of the iterated pairing
    defining `Ψ`. No packaged general convolution of a compactly supported
    distribution with an arbitrary distribution was found. The final conjunct then needs
    differentiation-through-convolution and a nonzero homogeneous solution;
    once the latter exists, the new addition lemma supplies the second
    solution. The intended witness is a regular constant distribution, but it is
    blocked by the same absent regular-distribution constructor. These are
    genuine topological-distribution assemblies, not merely algebraic
    rewriting, so the remaining conjunction stays honestly open.
    -/
    sorry
