import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# APM a01J04 — decay of derivatives after subtracting a simple pole

The hypothesis explicitly pins the meromorphic function to its Laurent
principal part at `1`: `f(z) = λ/(z-1) + g(z)` with `g` entire and `λ ≠ 0`.
Thus `f` is analytic away from `1`, has a simple pole there, and has residue
`λ`.  The conclusion is the limit requested in the source.

## Statement repairs

None.

## Encoding questions

None. Complex modulus is written with the current norm notation, and the
neighbourhood filter is the explicit `Filter.nhds`.
-/

open Filter

theorem apm_a01j04
    (f g : ℂ → ℂ) (lam : ℂ)
    (hlam : lam ≠ 0)
    (hg : Differentiable ℂ g)
    (hf : ∀ z : ℂ, f z = lam / (z - 1) + g z) :
    ∀ T : ℝ, 0 < T →
      Tendsto
        (fun n : ℕ ↦
          T ^ n *
            ‖(-1 : ℂ) ^ n * iteratedDeriv n f 2 /
                (Nat.factorial n : ℂ) - lam‖)
        atTop (nhds 0) := by
  sorry
