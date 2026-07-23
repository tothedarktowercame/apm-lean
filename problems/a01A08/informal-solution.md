

This is identical to **apm-a00J04**. The solution is the same.

# APM a01A08 = a00J04: Components of the complement of a polynomial lemniscate

## Why It's Hard

The level set L = {|p(z)| = 1} can be topologically complex — self-intersecting, with multiple loops. Counting connected components of ℂ \ L requires linking the topology to the algebraic degree. The key constraint comes from two principles: the maximum modulus principle (which kills bounded superlevel components) and the minimum modulus principle (which forces each bounded sublevel component to contain a root).

## The Key Insight

Every component of ℂ \ L is either sublevel ({|p| < 1}) or superlevel ({|p| > 1}), by continuity of |p| and connectedness. The maximum modulus principle implies there are no bounded superlevel components, so there is exactly one (unbounded) superlevel component. The minimum modulus principle forces each sublevel component to contain at least one root of p. Since p has at most N roots, there are at most N sublevel components. Total: at most N + 1.

## Complete Proof

**Theorem.** Let p(z) be a polynomial of degree N ≥ 1 and L = {z ∈ ℂ : |p(z)| = 1}. Then ℂ \ L has at most N + 1 connected components.

**Proof.**

**Step 1: Each component is purely sublevel or superlevel.** If U is a connected component of ℂ \ L, then |p| : U → (0,∞) \ {1} is continuous on the connected set U, mapping into the disconnected set (0,1) ∪ (1,∞). So |p| < 1 throughout U or |p| > 1 throughout U.

**Step 2: Exactly one superlevel component.** Suppose U is a bounded component with |p| > 1 on U. Then ∂U ⊂ L, so |p| = 1 on ∂U. By the maximum modulus principle applied to p on the bounded open set U: |p(z)| ≤ max\_{∂U} |p| = 1 for all z ∈ U. This contradicts |p| > 1 on U. So every superlevel component is unbounded.

Since |p(z)| → ∞ as |z| → ∞, the set {|z| > R} ⊂ {|p| > 1} for R large enough, and {|z| > R} is connected. Every unbounded superlevel component meets {|z| > R}, so there is exactly one superlevel component.

**Step 3: Each sublevel component contains a root.** Let U be a component with |p| < 1 on U. Since |p(z)| → ∞, U is bounded. On the compact closure, |p| achieves its minimum. On ∂U ⊂ L, |p| = 1; on U, |p| < 1. So the minimum is attained in U. If p never vanished on U, then 1/p would be holomorphic on U and continuous on the closure, with |1/p| = 1 on ∂U and |1/p| > 1 on U — contradicting the maximum modulus principle for 1/p. So p has at least one root in U.

**Step 4: Count.** Distinct components contain distinct roots. The polynomial p has at most N roots. So: at most N sublevel components + exactly 1 superlevel component = at most N + 1. ∎

## What Connects

**To potential theory.** L is a *lemniscate*; log|p| is a subharmonic function whose level sets govern the topology. The Green's function of the unbounded component with pole at ∞ is (1/N)log|p(z)|.

**To polynomial dynamics.** The filled Julia set K(p) ⊂ {|p| ≤ 1} in a suitable normalisation. The N+1 bound is the first step in understanding its topology.

**Sharpness.** For p(z) = (z − a₁)···(z − aₙ) with widely separated roots, {|p| < 1} has exactly N components (one island per root), achieving the bound.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.AbsMax

open Complex Polynomial Set Topology

noncomputable section

variable {p : ℂ[X]} (hp : 0 < p.natDegree)

def lemniscate (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖Polynomial.aeval z p‖ = 1}

def superlevel (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | 1 < ‖Polynomial.aeval z p‖}

def sublevel (p : ℂ[X]) : Set ℂ :=
  {z : ℂ | ‖Polynomial.aeval z p‖ < 1}

/-- Each connected subset of ℂ \ L lies entirely in the sublevel
    or entirely in the superlevel set. -/
lemma isPreconnected_subset_superlevel_or_sublevel
    {S : Set ℂ} (hS : IsPreconnected S) (hSL : Disjoint S (lemniscate p)) :
    S ⊆ superlevel p ∨ S ⊆ sublevel p := by
  sorry

/-- Maximum modulus principle: no bounded superlevel component exists. -/
lemma not_isBounded_superlevel_component
    {U : Set ℂ} (hU : IsOpen U) (hC : IsConnected U)
    (hS : U ⊆ superlevel p) (hB : frontier U ⊆ lemniscate p) :
    ¬Bornology.IsBounded U := by
  sorry

/-- The superlevel set is connected. -/
lemma isConnected_superlevel (hp : 0 < p.natDegree) :
    IsConnected (superlevel p) := by
  sorry

/-- The sublevel set is bounded. -/
lemma isBounded_sublevel (hp : 0 < p.natDegree) :
    Bornology.IsBounded (sublevel p) := by
  sorry

/-- Minimum modulus: each sublevel component contains a root. -/
lemma exists_root_in_sublevel_component
    {U : Set ℂ} (hU : IsOpen U) (hC : IsConnected U)
    (hS : U ⊆ sublevel p) (hB : Bornology.IsBounded U) :
    ∃ z ∈ U, Polynomial.aeval z p = 0 := by
  sorry

/-- Distinct sublevel components contain distinct roots. -/
lemma injective_root_of_disjoint_sublevel
    {U V : Set ℂ} (hUV : Disjoint U V)
    (hU : IsConnected U) (hV : IsConnected V)
    (hUS : U ⊆ sublevel p) (hVS : V ⊆ sublevel p)
    {zu zv : ℂ} (hzu : zu ∈ U) (hzv : zv ∈ V)
    (hru : Polynomial.aeval zu p = 0) (hrv : Polynomial.aeval zv p = 0) :
    zu ≠ zv := by
  sorry

/-- A polynomial of degree N has at most N roots. -/
lemma card_roots_le : (Polynomial.roots p).toFinset.card ≤ p.natDegree := by
  sorry

/-- Main theorem: ℂ \ L has at most N + 1 connected components. -/
theorem connectedComponents_complement_lemniscate_le :
    Nat.card (ConnectedComponents (lemniscate p)ᶜ) ≤ p.natDegree + 1 := by
  sorry

end
```

**Mathlib notes:** Identical to a00J04. `ConnectedComponents` counts connected components; `Polynomial.aeval z p` evaluates p at z; `‖·‖` on ℂ is the complex absolute value. The proof chains: 1 superlevel (by max modulus) + at most N sublevel (by min modulus + root counting) = at most N + 1.
