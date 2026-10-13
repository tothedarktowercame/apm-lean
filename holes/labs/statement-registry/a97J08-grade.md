# a97J08 statement fidelity grade

| id | grade | one-line reason | repair classification |
|---|---|---|---|
| a97J08 | faithful | Hurwitz/Rouché claim stated as given: open simply connected D, rectifiable Jordan curve in D, analytic F n → g locally uniformly on D, g ≠ 0 on Γ, eventual equality of zero counts (with multiplicity) inside Γ | n/a (not REPAIRED; header says "Statement repairs: None.") |

## Evidence: a97J08

Source: `problems/a97J08/lean/Main.lean` (worktree `/home/joe/worktrees/apm-lean/lemmas`), lines 29-42 and 3812-3824. No STATEMENT-REPAIR.md is present.

```lean
theorem apm_a97j08 (D : Set ℂ) (γ : ℝ → ℂ) (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hD_open : IsOpen D)
    (hD_simplyConnected : IsSimplyConnected D)
    (hγ_cont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγ_closed : γ 0 = γ 1)
    (hγ_simple : Set.InjOn γ (Ico (0 : ℝ) 1))
    (hγ_rectifiable : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hγD : apm_a97j08_curveImage γ ⊆ D)
    (hF_analytic : ∀ n, DifferentiableOn ℂ (F n) D)
    (hF_tendsto : TendstoLocallyUniformlyOn F g atTop D)
    (hg_ne : ∀ z ∈ apm_a97j08_curveImage γ, g z ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      apm_a97j08_zeroCount (F n) (apm_a97j08_curveInterior γ) =
        apm_a97j08_zeroCount g (apm_a97j08_curveInterior γ)
```

Definitions used:

```lean
def apm_a97j08_curveImage (γ : ℝ → ℂ) : Set ℂ := γ '' Icc (0 : ℝ) 1
def apm_a97j08_curveInterior (γ : ℝ → ℂ) : Set ℂ :=
  {z | z ∉ apm_a97j08_curveImage γ ∧
    Bornology.IsBounded (connectedComponentIn (apm_a97j08_curveImage γ)ᶜ z)}
def apm_a97j08_zeroCount (f : ℂ → ℂ) (U : Set ℂ) : ℤ :=
  ∑ᶠ z : ℂ, max (MeromorphicOn.divisor f U z) 0
```

Hypotheses mapped to problem.md:
- "open simply connected D": `IsOpen D`, `IsSimplyConnected D`.
- "simple closed rectifiable path γ:[0,1]→D": continuity on [0,1], `γ 0 = γ 1`, injectivity on [0,1), bounded variation on [0,1] (standard rectifiability), image ⊆ D. This is a standard encoding, not a restriction.
- "f_n analytic on D": `DifferentiableOn ℂ (F n) D` on open D, which is equivalent.
- "converge uniformly to g on compact subsets of D": `TendstoLocallyUniformlyOn ... D`. On an open subset of ℂ (locally compact) this is equivalent to uniform convergence on compacts.
- "g(z) ≠ 0 on Γ": `hg_ne`.
- No extra hypothesis. In particular g is not assumed analytic or nonzero on the interior. Analyticity of g follows from the hypotheses (a locally uniform limit of holomorphic functions is holomorphic), so nothing is assumed that the problem does not give.

Conclusion: "inside Γ" is encoded as the union of the bounded components of ℂ∖Γ. For a Jordan curve that is exactly the single Jordan interior, so this is faithful and does not presuppose the Jordan curve theorem. Zeros are counted with multiplicity through the positive part of the divisor, which is the usual reading of "number of zeros" in a Rouché/Hurwitz setting.

Possible degeneracies checked:
- `MeromorphicOn.divisor` gives 0 on functions that are not meromorphic. Here every F n is holomorphic on D. The file proves closure(interior) ⊆ D from simple connectivity (around lines 3800-3810), so the divisor is the genuine zero divisor on that set.
- `finsum` gives 0 when the support is infinite. The zero sets are finite here: the closure of the interior is compact in D, and g cannot vanish identically on a component, because by continuity it would then vanish on Γ.

So the counts are not trivially 0 = 0, and the conclusion is the real claim, neither weakened nor strengthened.

Grade: faithful.
