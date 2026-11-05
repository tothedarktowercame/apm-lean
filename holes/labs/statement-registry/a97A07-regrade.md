Grade: faithful

Statement graded: `apm_a97A07` in `problems/a97A07/lean/Main.lean` (registered by
claude-14, 2026-11-05), against `problems/a97A07/problem.md`. Read-only regrade,
2026-11-05. Nothing built or run; every check below was done by reading.

The only deviation from problem.md is `P.natDegree ≤ n - 1` in place of "degree
n - 1". The printed claim is false (checked below), so this deviation is the
forced correction, not a narrowing. Every other hypothesis is either the
problem's own hypothesis or something the printed integral already presumes
(a rectifiable curve, positive orientation).

## 1. Jordan curve as 1-periodic, Lipschitz, injective on [0,1): fair

```lean
structure apm_a97A07_IsJordanCurve (γ : ℝ → ℂ) : Prop where
  periodic : Function.Periodic γ 1
  injOn : Set.InjOn γ (Set.Ico 0 1)
  lipschitz : ∃ K, LipschitzWith K γ
```

Periodic with period 1 and injective on `[0,1)` is a simple closed curve
(continuity comes from Lipschitz). The problem integrates over γ, which in the
classical setting requires γ rectifiable. A rectifiable Jordan curve,
reparametrised by arc length and rescaled to period 1, is Lipschitz with
constant equal to its length, and it stays injective on `[0,1)` because an
injective curve has no intervals of constancy. The integral is invariant under
orientation-preserving reparametrisation, so nothing is lost. Lipschitz also
makes γ absolutely continuous, so `∫ g(γ t) * deriv γ t` is the contour integral
(Rademacher: `deriv γ` is the true derivative a.e., bounded by K). K = 0 is
excluded by `injOn`. Not a real restriction. (One could argue that for f
analytic on a neighbourhood of the closed region the integral over a
non-rectifiable Jordan curve can be defined by approximation, but that is not a
reading a prelim intends.)

## 2. `apm_a97A07_inside` is the interior: yes

```lean
def apm_a97A07_inside (γ : ℝ → ℂ) : Set ℂ :=
  {w | w ∉ range γ ∧ Bornology.IsBounded (connectedComponentIn (range γ)ᶜ w)}
```

By the Jordan curve theorem the complement of `range γ` has exactly two
components, one bounded. The set is the union of the bounded components, i.e.
the interior. Correct.

## 3. `PositivelyOriented`: fair encoding, does not carry the core, satisfiable

```lean
def apm_a97A07_PositivelyOriented (γ : ℝ → ℂ) : Prop :=
  ∃ w ∈ apm_a97A07_inside γ,
    (1 / (2 * π * I)) * ∫ t in (0 : ℝ)..1, (γ t - w)⁻¹ * deriv γ t = 1
```

The printed integral presumes positive orientation: with the reverse
orientation P(z_k) = -f(z_k) and the claim fails, so some orientation
hypothesis is required. The formula is the standard winding number. For a
Jordan curve the winding number is ±1 and constant on the (connected) interior,
so "some interior point" is equivalent to "every interior point", and every
Jordan curve traversed counterclockwise satisfies it.

It does not supply the main content. From it the prover still has to derive
winding number 1 about each `zs k` (Jordan curve theorem plus local constancy of
the index) and winding number 0 about every point outside the domain of
analyticity (the unbounded component), and then apply the homology form of the
Cauchy integral formula to f. It only fixes the sign, which the problem leaves
implicit.

## 4. `AnalyticOnNhd ℂ f (inside ∪ range γ)`: equals "analytic inside and on γ"

```lean
(f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (apm_a97A07_inside γ ∪ range γ))
```

`AnalyticOnNhd` means `AnalyticAt` at each point of the set, so f is analytic on
an open set containing the closed region interior ∪ curve. That is the standard
meaning of "analytic inside and on γ". Exact match.

## 5. `Q` and `P` compute the printed integral; no Lean-semantics traps

```lean
def apm_a97A07_Q {n : ℕ} (zs : Fin n → ℂ) (ζ z : ℂ) : ℂ :=
  if z = ζ then (Polynomial.derivative (apm_a97A07_p zs)).eval ζ
  else ((apm_a97A07_p zs).eval ζ - (apm_a97A07_p zs).eval z) / (ζ - z)

def apm_a97A07_P ... (z : ℂ) : ℂ :=
  (1 / (2 * π * I)) * ∫ t in (0 : ℝ)..1,
    f (γ t) / (apm_a97A07_p zs).eval (γ t) * apm_a97A07_Q zs (γ t) z * deriv γ t
```

- Q: `(p(ζ) - p(z))/(ζ - z)` is a polynomial in (ζ, z) whose diagonal value is
  p'(ζ), so Q equals that two-variable polynomial everywhere. The `z = ζ`
  branch is the continuous extension, not a junk value. It only matters when z
  lies on the curve, and then only at the t in [0,1] with γ t = z (at most two
  points, t = 0 and t = 1), a null set, so it does not affect the integral in
  any case.
- Division by `p(γ t)`: every node is in `inside`, which excludes `range γ`, so
  p(γ t) ≠ 0 for every t. No division by zero.
- `deriv γ`: junk value 0 only at non-differentiability points, a null set for
  Lipschitz γ.
- Integrability: f ∘ γ is continuous (f is continuous on `range γ`), 1/p ∘ γ
  is continuous, Q(γ t, z) is continuous in t, and `deriv γ` is measurable and
  bounded by K. The integrand is integrable on [0,1].
- `1 / (2 * π * I)` with π coerced to ℂ is 1/(2πi).

## 6. True as stated, including n = 0 and z on the curve

Writing Q(ζ, z) = Σ_{j<n} q_j(ζ) z^j gives P(z) = Σ_{j<n} c_j z^j with
c_j = (1/2πi)∫ f q_j / p dζ, a polynomial of natDegree ≤ n - 1. This holds for
every z, including z on the curve, because Q equals the polynomial identically.
At a node, p(z_k) = 0 gives Q(ζ, z_k) = p(ζ)/(ζ - z_k) for ζ on the curve, so
P(z_k) = (1/2πi)∫ f(ζ)/(ζ - z_k) dζ = Ind_γ(z_k) f(z_k) = f(z_k) by Cauchy, with
Ind = 1 obtained as in point 3.

n = 0: p = 1 (empty product), Q ≡ 0 (both branches: (1-1)/(ζ-z) = 0 and
derivative of 1 is 0), so P ≡ 0. The zero polynomial has natDegree 0 ≤ 0 - 1 = 0
(ℕ subtraction), and `∀ k : Fin 0` is vacuous. True.

## 7. No unsatisfiable hypotheses

Witness: γ t = exp(2πit) is 1-periodic, injective on [0,1), Lipschitz with
constant 2π. `inside` is the open unit disc. For w = 0 the winding integral is
(1/2πi)∫₀¹ e^{-2πit}·2πi e^{2πit} dt = 1, so `hpos` holds. Any distinct nodes in
the disc satisfy `hzs`, `hin`, and any entire f satisfies `hf`. The conclusion is
not trivial: it contains the Cauchy integral formula at each node.

## Defect counterexample check

n = 2, z₁ = 0, z₂ = 1/2, γ the unit circle counterclockwise, f ≡ 1.
p(ζ) = ζ² - ζ/2, and (p(ζ) - p(z))/(ζ - z) = ζ + z - 1/2. So

P(z) = (1/2πi)∫_γ (ζ + z - 1/2)/(ζ(ζ - 1/2)) dζ.

Residue at 0: (z - 1/2)/(-1/2) = 1 - 2z. Residue at 1/2: z/(1/2) = 2z. Sum: 1.
So P ≡ 1, degree 0 ≠ n - 1 = 1. Confirmed: the printed "degree n - 1" is false.
More generally P is the Lagrange interpolant of f at the nodes, and its degree
is exactly n - 1 only when the divided difference f[z₁,…,z_n] ≠ 0. The
registered `natDegree ≤ n - 1` is the forced correction. This instance satisfies
it (0 ≤ 1).
