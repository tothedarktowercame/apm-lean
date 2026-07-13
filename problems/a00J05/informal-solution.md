

# APM a00J04: Components of the complement of a polynomial lemniscate

## Why It's Hard

The level set L = {|p(z)| = 1} is a real-algebraic curve in ℂ ≅ ℝ², and counting connected components of its complement requires linking the topology of the curve to the algebra of the polynomial. The difficulty is that L can be complicated — it can self-intersect, have multiple loops, and its topology depends on the configuration of the roots of p. You cannot just "see" the answer from a picture. The key is to identify the right invariant that controls the component count.

## The Key Insight

The function |p(z)| is continuous and takes only the values "< 1" or "> 1" on each component of ℂ \ L (by the intermediate value theorem, since L is exactly where |p| = 1). So every component of ℂ \ L is either a "sublevel" component (where |p| < 1) or a "superlevel" component (where |p| > 1).

- **Superlevel components** ({|p| > 1}): there is exactly **one**, because |p(z)| → ∞ as |z| → ∞ (p has degree N ≥ 1), so all points with |p(z)| > 1 are connected to a large circle at infinity. More precisely, {|p| > R} is connected for large R (it's the complement of a compact set in a neighbourhood of ∞), and every point with |p(z)| > 1 can be connected to {|p| > R} by a path along which |p| stays > 1 (by the maximum principle / openness of |p| > 1).

- **Sublevel components** ({|p| < 1}): each must contain at least one root of p (because |p| achieves its minimum on each component by the minimum modulus principle — a nonconstant analytic function on a connected open set cannot attain an interior minimum of its modulus unless it vanishes). So the number of sublevel components is at most the number of roots of p, counted without multiplicity: at most **N**.

Total: at most N + 1.

## Complete Proof

**Theorem.** Let p(z) be a polynomial of degree N ≥ 1 and let L = {z ∈ ℂ : |p(z)| = 1}. Then ℂ \ L has at most N + 1 connected components.

**Proof.**

**Step 1: Each component is purely sublevel or purely superlevel.**

The function z ↦ |p(z)| is continuous on ℂ and equals 1 on L. If U is a connected component of ℂ \ L, then |p(z)| ≠ 1 for all z ∈ U, and since |p| is continuous and U is connected, |p(z)| is either strictly less than 1 on all of U or strictly greater than 1 on all of U (the continuous function |p| : U → ℝ \ {1} maps a connected set into a disconnected set {t > 0 : t ≠ 1} = (0,1) ∪ (1,∞), so it must land entirely in one piece). Note |p| > 0 on {|p| > 1} and |p| ≥ 0 on {|p| < 1}, but roots of p can have |p| = 0 < 1, which is fine.

Call a component **sublevel** if |p| < 1 on it, and **superlevel** if |p| > 1 on it.

**Step 2: There is exactly one superlevel component.**

Since deg p = N ≥ 1, we have |p(z)| → ∞ as |z| → ∞. Choose R large enough that |p(z)| > 1 for all |z| > R. The set {|z| > R} is connected (it is the complement of a closed disk), and it is contained in {|p| > 1}. Therefore every superlevel component of ℂ \ L must intersect {|z| > R}: if U is a superlevel component, pick z₀ ∈ U with |p(z₀)| > 1. Consider the set S = {z : |p(z)| > 1}. This set is open (preimage of (1,∞) under continuous |p|). The component U of ℂ \ L containing z₀ is contained in S. Since {|z| > R} ⊂ S and {|z| > R} is connected, {|z| > R} lies in a single component of S. Any bounded superlevel component U would be a bounded connected open subset of ℂ on which |p| > 1 everywhere. But then |p| achieves a minimum on the closure of U. On ∂U ⊂ L, |p| = 1, so |p| ≥ 1 on the closure. If |p| > 1 on U, the minimum on the closure is 1, achieved on ∂U. But then by continuity, there are points of U arbitrarily close to ∂U where |p| is close to 1, and since U is open and connected and {|z| > R} ⊂ {|p| > 1}, we need to argue more carefully. 

Here is a cleaner argument. Let V = {z ∈ ℂ : |p(z)| > 1}. This is open. We claim V is connected. Consider two points z₁, z₂ ∈ V. For R large enough, |z₁|, |z₂| < R and |p(z)| > 1 for all |z| = R. The function p maps the circle |z| = R to a curve that stays outside the closed unit disk. Connect z₁ to a point w₁ on the circle {|z| = R} by a path γ₁ from z₁ radially outward to the circle. Along this ray, once |z| is large enough, |p(z)| > 1. But this ray might dip below 1 somewhere. Instead: since V is open and |p(z)| > 1 at z₁, and |p(z)| → ∞ along any ray from the origin, consider t ↦ |p(tz₁/|z₁|)| for t ≥ |z₁|. This tends to ∞, so |p| > 1 for t large. But it might dip below 1.

Let me use a different approach. Every connected component of V is open. If a component U of V is bounded, then its boundary ∂U satisfies |p| = 1 on ∂U (since ∂U ⊂ L ∪ ∂{|p|>1} ⊂ L). So on the closure of U (compact, since U is bounded), the holomorphic function p satisfies |p| = 1 on ∂U and |p| > 1 on U. By the minimum modulus principle applied to 1/p (which is holomorphic and non-vanishing on U since |p| > 1 > 0 on U): |1/p| < 1 on U and |1/p| = 1 on ∂U, so 1/p achieves its maximum modulus on the boundary, which is consistent. But the *maximum* modulus principle applied to 1/p says |1/p| ≤ max\_{∂U} |1/p| = 1 on U. This just gives |p| ≥ 1 on U, which we know. 

The issue is that a bounded component of {|p| > 1} is not immediately excluded. But actually, by the maximum principle for |p|: if U is a bounded open set with |p| = 1 on ∂U, then |p| ≤ 1 on U (by the maximum modulus principle for p). But we assumed |p| > 1 on U — contradiction. **So there are no bounded superlevel components.** Therefore every superlevel component is unbounded, and since all unbounded components share the region {|z| > R} (which is connected), there is exactly one superlevel component.

**Step 3: Each sublevel component contains a root of p.**

Let U be a sublevel component, so U is a connected open set with |p(z)| < 1 for all z ∈ U. We claim p has a zero in U.

U is bounded: since |p(z)| → ∞, there exists R such that |p(z)| ≥ 1 for all |z| ≥ R, so {|p| < 1} ⊂ {|z| < R}, hence every sublevel component is bounded, thus has compact closure.

On the compact closure of U, the continuous function |p| achieves its minimum. On ∂U ⊂ L, |p| = 1. On U, |p| < 1. So the minimum of |p| on the closure of U is achieved at some interior point z₀ ∈ U, with |p(z₀)| < 1.

By the minimum modulus principle: if p is holomorphic and nonvanishing on a connected open set, then |p| cannot achieve an interior local minimum. Since |p| does achieve an interior minimum at z₀ (namely min on the closure of U), p must vanish somewhere in U. So p(z₀) = 0 (if z₀ is the minimizer) or p has a root somewhere in U.

More precisely: if p has no root in U, then 1/p is holomorphic on U and continuous on the closure of U (since |p| > 0 on the closure). By the maximum modulus principle for 1/p on U: |1/p(z)| ≤ max\_{∂U} |1/p| = 1 for all z ∈ U, i.e., |p(z)| ≥ 1 on U. But |p| < 1 on U — contradiction. So p must have at least one root in U.

**Step 4: Counting.**

The polynomial p has at most N roots (counting without multiplicity). Each sublevel component contains at least one root. Different components are disjoint, so distinct components contain distinct roots (a root in one component cannot be in another). Therefore there are at most N sublevel components.

Together with the exactly 1 superlevel component: at most N + 1 components total. ∎

## What Connects

**To potential theory.** The set L = {|p| = 1} is a *lemniscate*, a level set of the logarithmic potential log|p|. The sublevel components are the "basins" of the roots, and the superlevel component is the basin of infinity. The Green's function of the complement of {|p| ≤ 1} with pole at infinity is exactly (1/N) log|p(z)|.

**To polynomial dynamics.** The filled Julia set of p is K = {z : |p^n(z)| does not tend to ∞}, and the lemniscate {|p| ≤ 1} is its first approximation (the "level-1 filled Julia set"). The bound N + 1 on components is the first step in understanding the topology of Julia sets.

**To the argument principle.** The bound N on sublevel components is tight: p(z) = zⁿ gives exactly N sublevel components (the N sectors where |z| < 1 under the Nth-root map). Adding the unbounded component gives N + 1 exactly.

**Sharpness.** The bound N + 1 is achieved by p(z) = zⁿ: the sublevel region {|z|ⁿ < 1} = {|z| < 1} is a single disk (so for this particular polynomial the sublevel set has 1 component, not N). To get closer to N + 1, consider p(z) = (z - a₁)···(z - aₙ) with widely separated roots: each root has its own sublevel island, giving N sublevel + 1 superlevel = N + 1 components.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex Polynomial Set Topology Filter

noncomputable section

variable {p : ℂ[X]} (hp : 0 < p.natDegree)

/-- The lemniscate of a polynomial. -/
def lemniscate (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖Polynomial.aeval z p‖ = 1}

/-- The superlevel set {|p(z)| > 1}. -/
def superlevel (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | 1 < ‖Polynomial.aeval z p‖}

/-- The sublevel set {|p(z)| < 1}. -/
def sublevel (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖Polynomial.aeval z p‖ < 1}

/-- Each component of ℂ \ L is entirely sublevel or entirely superlevel. -/
lemma isPreconnected_subset_superlevel_or_sublevel
    {S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) :
    S ⊆ superlevel p ∨ S ⊆ sublevel p := by
  sorry

/-- The maximum modulus principle rules out bounded superlevel components:
    if U is bounded, open, connected, with |p| = 1 on ∂U and |p| > 1 on U,
    this contradicts the maximum modulus of p on the closure of U. -/
lemma not_isBounded_of_superlevel_component
    {U : Set ℂ} (hU_open : IsOpen U)
    (hU_conn : IsConnected U)
    (hU_super : U ⊆ superlevel p)
    (hU_bdy : frontier U ⊆ lemniscate p) :
    ¬Bornology.IsBounded U := by
  sorry

/-- The superlevel set {|p(z)| > 1} is connected.
    Key: all bounded components are ruled out by the maximum principle;
    the unbounded part is connected because |p(z)| → ∞. -/
lemma isConnected_superlevel (hp : 0 < p.natDegree) :
    IsConnected (superlevel p) := by
  sorry

/-- The sublevel set is bounded (contained in a large disk),
    because |p(z)| → ∞ as |z| → ∞. -/
lemma isBounded_sublevel (hp : 0 < p.natDegree) :
    Bornology.IsBounded (sublevel p) := by
  sorry

/-- The minimum modulus principle forces each connected
    component of the sublevel set to contain a root of p. -/
lemma exists_root_in_sublevel_component
    {U : Set ℂ} (hU_open : IsOpen U)
    (hU_conn : IsConnected U)
    (hU_sub : U ⊆ sublevel p)
    (hU_bdd : Bornology.IsBounded U) :
    ∃ z ∈ U, Polynomial.aeval z p = 0 := by
  sorry

/-- Distinct sublevel components contain distinct roots. -/
lemma injective_root_of_sublevel_components
    {U V : Set ℂ} (hU : IsConnected U) (hV : IsConnected V)
    (hUV : Disjoint U V)
    (hU_sub : U ⊆ sublevel p) (hV_sub : V ⊆ sublevel p)
    (hU_open : IsOpen U) (hV_open : IsOpen V)
    (hU_bdd : Bornology.IsBounded U) (hV_bdd : Bornology.IsBounded V)
    {zu zv : ℂ} (hzu : zu ∈ U) (hzv : zv ∈ V)
    (hru : Polynomial.aeval zu p = 0) (hrv : Polynomial.aeval zv p = 0) :
    zu ≠ zv := by
  sorry

/-- A polynomial of degree N has at most N roots (without multiplicity). -/
lemma card_roots_le_natDegree :
    (Polynomial.roots p).toFinset.card ≤ p.natDegree := by
  sorry

/-- Main theorem: ℂ \ lemniscate(p) has at most N + 1 connected components.
    Stated: any family of pairwise disjoint connected open subsets of ℂ \ L
    has cardinality at most natDegree p + 1. -/
theorem connectedComponents_complement_lemniscate_le :
    Nat.card (ConnectedComponents (lemniscate p)ᶜ) ≤ p.natDegree + 1 := by
  sorry

end
```

**Mathlib notes:**

- `Polynomial.aeval z p` evaluates polynomial p at z; `‖·‖` on ℂ is `Complex.abs`, so `‖Polynomial.aeval z p‖ = |p(z)|`.
- `ConnectedComponents` is the type of connected components of a topological space (here the subspace `(lemniscate p)ᶜ`); `Nat.card` counts them.
- The maximum modulus principle in Mathlib lives in `Mathlib.Analysis.Complex.AbsMax` (as `Complex.eventually_eq_of_isLocalMax_norm` and related).
- `Polynomial.roots` gives the multiset of roots; `.toFinset.card` counts without multiplicity.
- The proof architecture: `isConnected_superlevel` gives 1 superlevel component; `exists_root_in_sublevel_component` + `injective_root_of_sublevel_components` + `card_roots_le_natDegree` give at most N sublevel components.