# Grading batch 3: m98A04

| id | grade | decl | one-line reason | prelim-defect |
|---|---|---|---|---|
| m98A04 | faithful | `apm_m98a04` (problems/m98A04/lean/Main.lean) | Encodes (a) `D^α(T*φ) = (D^αT)*φ = T*(D^αφ)` for every multiindex, (b) `T*φ ∈ C^∞`, (c) `sin*cos = π sin x` over Mathlib `Distribution`/`TestFunction` on `⊤ : Opens`, smoothness `⊤ : ℕ∞` (C^∞, not ω); statement byte-identical to bank version (neutral). | Yes: the middle term of (a), printed `∂^α ∗ φ`, is missing `T`; repaired to `(D^α T) ∗ φ` (documented in the Main.lean "Statement repairs" block, matches the informal solution). |

## Evidence

- **Objects.** `T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤` and `φ : TestFunction (⊤ : Opens …) ℝ ⊤`. In Mathlib, `TestFunction Ω F n` and `Distribution Ω F n` take `n : ℕ∞`, so `⊤` means C^∞ (Mathlib's `𝓓'(Ω,F) = Distribution Ω F ⊤`). There is no ω issue. Part (b) uses `ContDiff ℝ ∞ h` with `∞` from `open scoped ContDiff`, which is the smooth order.
- **Convolution.** `apm_m98a04_IsConvolution T φ h := ∀ x ψ, (∀ y, ψ y = φ (x - y)) → h x = T ψ`. This is `(T*φ)(x) = ⟨T_y, φ(x−y)⟩`, with the correct variable and the correct reflection. Such a ψ always exists (`apm_m98a04_translateReflect`), so `h` is pinned down and the condition is not vacuous.
- **Distributional derivative.** `apm_m98a04_IsDistributionalPartial indices T DT := ∀ ψ dψ, (∀ x, dψ x = partialList indices ψ x) → DT ψ = (-1)^indices.length * T dψ`. The sign `(-1)^{|α|}` is the standard one. Because `D^αψ` is always a test function, `DT` is uniquely `D^αT`, and nothing is assumed beyond that.
- **Derivatives.** `partialList` iterates `fderiv … (EuclideanSpace.single i 1)`. Lists of coordinates cover all multiindices, and order does not matter for C^∞ functions. Because `h` is C^∞, the classical `fderiv` is the true derivative.
- **Conclusion.** `partialList indices h = hDT ∧ hDT = hφ`, where `hDT = (D^αT)*φ` and `hφ = T*(D^αφ)`. This is the repaired identity in (a). All the existentials (`h`, `DT`, `dφ`, `hDT`, `hφ`) are uniquely determined by their defining predicates, so they do not weaken the claim. There are no hypotheses at all, so none of them carries the core content.
- **(c).** `∀ x, ∫ y in 0..2π, sin y * cos (x - y) = π * sin x`. This matches the problem's `∫_0^{2π} f(y) g(x−y) dy`, and the computed answer is supplied as the target, which is the right encoding for "compute".
- **History.** `git log` shows 26f037b1c (statement bank) as the oldest commit, followed by codex partials and then ad793a6e8 (closed). Diffing the theorem statement and the three definitions it uses (`partialList`, `IsConvolution`, `IsDistributionalPartial`) between 26f037b1c and HEAD gives no differences. Later commits only add helper definitions and lemmas used by the proof, one import (`ConstructionTargets.TestFunctionTranslation`), and `open` lines. Classification: **neutral** (no change to the statement).
