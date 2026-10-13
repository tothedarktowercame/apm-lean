# Statement repair and blueprint for m96A02

## Triage verdict: false and unfaithful

The checked-in Lean statement has two independent defects.

First, the two metric-space clauses quantify over complete metric spaces
without assuming they are nonempty. The compiled `Refute.lean` takes
`M = ULift Empty` and its unique self-map. The contraction inequality is
vacuous (with constant zero), but the claimed fixed point would inhabit an
empty type.

Second, the source asks for a solution on the interval with initial value at
zero. The Lean predicate imposed the ODE only on `(0,1)` and fixed `u(0)`, but
did not require continuity at `1`, while uniqueness was asserted on `[0,1]`.
For `f=0`, `u₀=0`, the zero function and the function equal to zero except
with value one at `1` both satisfied the old predicate but disagreed at the
right endpoint.

Thus adding only `Nonempty M` would not make the complete theorem true.

## Repair

`RevisedMain.lean` makes two minimal source-warranted changes:

- adds `[Nonempty M]` to the complete metric spaces in parts (a) and (b);
- adds `ContinuousOn u (Icc 0 1)` to `apm_m96a02_Solves`.

The first is the conventional implicit meaning of a metric space on which a
fixed-point theorem asserts existence. The second records the standard
regularity inherent in “solution on `[0,1]`” and closes only the unconstrained
endpoint gap; the differential equation remains required exactly on the
source interval `0<t<1`.

Degenerate checks:

- `ULift Empty` is rejected because it has no `Nonempty` instance;
- singleton spaces satisfy the repaired Banach conclusion, with their unique
  point as the fixed point;
- for `f=0`, continuity plus the zero derivative on `(0,1)` and `u(0)=u₀`
  forces the constant solution through the endpoint `1`;
- `N=1` in part (b) reduces to ordinary Banach, while the assumption `1≤N`
  excludes the irrelevant zeroth iterate.

## Remaining lemmas

### `apm_m96A02_banach_fixed_point`

**Statement.** A contraction of a nonempty complete metric space has a unique
fixed point, and every orbit converges to it.

**Proof sketch.** Unpack the real contraction constant `k≥0`, form the
nonnegative real `⟨k,hk⟩`, and package the inequality as
`ContractingWith`. Then use `ContractingWith.fixedPoint_isFixedPt`,
`ContractingWith.tendsto_iterate_fixedPoint`, and
`ContractingWith.fixedPoint_unique`. Reverse the last equality where needed
to match the theorem's orientation.

**Estimate.** 50--90 lines.

**Dependencies.** Definitions and Mathlib's contracting-map API only.

**Truth check.** On a singleton the conclusion computes directly. The empty
counterexample is now excluded. The hand proof is the usual geometric Cauchy
estimate with ratio `k<1`.

### `apm_m96A02_iterate_contraction_fixed_point`

**Statement.** If a positive iterate `T^[N]` is a contraction on a nonempty
complete metric space, then `T` has exactly one fixed point.

**Proof sketch.** Apply the Banach API to `T^[N]`. Mathlib already provides
`ContractingWith.isFixedPt_fixedPoint_iterate`, which proves that the fixed
point of the iterate is fixed by `T`. Alternatively, use
`T^[N] (T x)=T (T^[N] x)` and uniqueness for the iterate. Any fixed point of
`T` is fixed by every positive iterate, so uniqueness transfers back.

**Estimate.** 60--110 lines.

**Dependencies.** Definitions and Mathlib's contracting-map/iterate API. Its
statement is independent of the first remaining lemma and can be proved
directly from the same API.

**Truth check.** For `N=1` it is Banach. For the two-cycle map on a two-point
space, `T²=id` is not a contraction with constant below one, showing why the
contraction hypothesis—not merely periodicity—is essential.

### `apm_m96A02_lipschitz_ode`

**Statement.** Every globally Lipschitz `f : ℝ→ℝ` and initial value has a
solution continuous on `[0,1]`, differentiable with `u'=f∘u` on `(0,1)`, and
unique on `[0,1]`.

**Proof sketch.** Use the Picard operator
`P(u)(t)=u₀+∫₀ᵗf(u(s))ds` on continuous functions on `[0,1]`. Prove by
induction the iterated estimate
`‖P^[n]u-P^[n]v‖ ≤ L^n/n! * ‖u-v‖`; choose `N` with `L^N/N!<1`, and apply the
iterate-contraction theorem. The fixed-point equation and the fundamental
theorem of calculus give the required derivatives and continuity. For
uniqueness, either use the same fixed-point uniqueness after converting any
solution to the integral equation, or apply the Grönwall results in
`Mathlib.Analysis.ODE.Gronwall`. Extend the interval function arbitrarily
outside `[0,1]`; `apm_m96a02_Solves` observes only the interval.

Mathlib's local construction in `Mathlib.Analysis.ODE.PicardLindelof` can
replace the explicit Picard-space construction, but its local ball parameters
still need globalization from the global Lipschitz bound. The direct iterate
argument mirrors the source and part (b) most closely.

**Estimate.** 240--320 lines.

**Dependencies.** Definitions plus standard interval-integral and continuous-
map completeness APIs. Its statement is independent of the first two lemmas;
the proof may reproduce or call the iterate fixed-point bridge after merging.

**Truth check.** For `f=0`, the unique solution is constant `u₀`. For
`f(x)=x`, it is `u₀ exp(t)`, which exists on the full interval for arbitrary
Lipschitz constant one. The endpoint-discontinuous former counterexample is
excluded by `ContinuousOn`.

## Dependency layers

- **Layer 1 (parallel):** all three remaining lemmas. Each has a standalone
  statement using only the definitions and repaired hypotheses.
- **Layer 2:** the main theorem is the conjunction of those lemmas and is
  already assembled without `sorry`.

## Confidence and doubt

Both repairs are necessary and exactly match the source's intended objects. I
am fully confident in the three mathematical statements. The ODE lemma is the
engineering risk: a direct Picard formalization is near the upper end of one
session, and reconciling Mathlib's interval-valued continuous-function spaces
with the global `ℝ→ℝ` output may add boilerplate. The local Picard–Lindelöf API
is available, but globalization and conversion to the custom `Solves`
predicate still require substantial work.

## Compile gates and axioms

All files compile:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m96A02/Refute.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m96A02/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/m96A02/Blueprint.lean
```

Output of `#print axioms apm_m96a02`:

```text
'apm_m96a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The blueprint main theorem has no `sorry`; `sorryAx` enters only through the
three named lemmas.
