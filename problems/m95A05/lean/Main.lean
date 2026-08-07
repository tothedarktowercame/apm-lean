import Mathlib

/-!
# APM m95A05: coercivity on a reflexive Banach space

## Statement repairs

None.

## Encoding questions

Mathlib does not package topological reflexivity as a typeclass. It is encoded
directly and without weakening as surjectivity of the canonical continuous
linear isometry `V → V''`.
-/

noncomputable section

/-- Coercivity bounds the operator from below.  This is the quantitative
input both for injectivity and for closedness of the range. -/
lemma apm_m95a05_norm_le_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] StrongDual ℝ V) (c : ℝ)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v) (v : V) :
    c * ‖v‖ ≤ ‖A v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have heval : A v v ≤ ‖A v‖ * ‖v‖ := by
    exact (le_abs_self (A v v)).trans (by
      simpa [Real.norm_eq_abs] using (A v).le_opNorm v)
  have hmul : (c * ‖v‖) * ‖v‖ ≤ ‖A v‖ * ‖v‖ := calc
    (c * ‖v‖) * ‖v‖ = c * ‖v‖ ^ 2 := by ring
    _ ≤ A v v := hcoercive v
    _ ≤ ‖A v‖ * ‖v‖ := heval
  nlinarith

lemma apm_m95a05_injective
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] StrongDual ℝ V) (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v) :
    Function.Injective A := by
  intro x y hxy
  have hzero : A (x - y) = 0 := by simpa using sub_eq_zero.mpr hxy
  have hbound := apm_m95a05_norm_le_apply A c hcoercive (x - y)
  rw [hzero, norm_zero] at hbound
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem apm_m95a05
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (hrefl : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V))
    (A : V →L[ℝ] StrongDual ℝ V)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v)
    (f : StrongDual ℝ V) :
    ∃! u : V, A u = f := by
  /-
  Boundary (closer hop 1): `apm_m95a05_norm_le_apply` now compiles the
  coercivity estimate `c * ‖v‖ ≤ ‖A v‖`, using the dual operator-norm bound,
  and `apm_m95a05_injective` derives uniqueness.  Thus the quantitative lower
  bound and the entire uniqueness half of the theorem are closed.

  The remaining existence argument is the closed-range/reflexivity route:
  use the lower bound and completeness to prove `Set.range A` closed; if it is
  proper, Hahn--Banach must produce a nonzero member of `V''` annihilating the
  range; use `hrefl` to write it as evaluation at `w : V`, and contradict
  coercivity by testing at `A w`.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets`, the closed-range Hilbert
  proof in `m96A03`, the dual-annihilator partial development in `m03J04`,
  Mathlib's Banach-operator, double-dual, and Hahn--Banach sources, and git
  history found no packaged normed-Banach theorem producing the required
  nonzero annihilator of an arbitrary proper closed range.  `m96A03` uses
  Hilbert orthogonal complements and therefore does not apply to `StrongDual`.

  Original boundary:
  SKIPPED: Lax-Milgram theorem on reflexive Banach space.
  -- A: V→V' coercive (⟨Av,v⟩ ≥ c‖v‖²), f∈V'. Show ∃! u: Au=f.
  -- Proof: coercivity ⟹ A injective; reflexivity + coercivity ⟹ A surjective
  -- (via bounded inverse / open mapping theorem). This is essentially Lax-Milgram.
  -- Blocker: requires Lax-Milgram theorem (NOT in Mathlib), open mapping theorem
  -- application, reflexivity hypothesis manipulation with double dual surjectivity.
  APIs: `NormedSpace.inclusionInDoubleDual`, `ContinuousLinearMap`, `StrongDual`.
  -/
  sorry
