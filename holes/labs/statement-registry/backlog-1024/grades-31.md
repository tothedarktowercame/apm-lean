| id | grade | one-line reason | repair classification if any |
|---|---|---|---|
| m99J05 | faithful | For an arbitrary real Hilbert space and continuous linear functional, it states existence and uniqueness of the quadratic's minimizer and exactly characterizes minimizers by the Riesz equation. | — |

### m99J05

The registered quadratic is exactly
`(1 / 2 : ℝ) * ‖v‖ ^ 2 - f v` (`Main.lean:18-20`), and minimizer means
`∀ v : V, apm_m99J05_quadratic f u ≤ apm_m99J05_quadratic f v`
(`Main.lean:22-24`). For an arbitrary real inner-product space with
`[CompleteSpace V]` and `f : V →L[ℝ] ℝ`, the theorem asserts
`∃! u : V, apm_m99J05_isMinimizer f u` and, for every `u`, the equivalence
between being a minimizer and `∀ v : V, inner ℝ u v = f v`
(`Main.lean:26-32`). Thus it contains all three requested claims: unique
existence, necessity of the variational equation, and its converse. The
statement is unchanged from the initial statement-bank commit `408f01fe0`;
later commits only replace its proof placeholder. No theorem-dependent
`axiom`, `opaque`, or sorry-typed definition was found.
