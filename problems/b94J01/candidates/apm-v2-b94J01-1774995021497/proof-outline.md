# Proof Outline: b94J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 'b94J01
 :frame-id 'apm-v2-b94J01-1774995021497
 :goal "Classify finite abelian groups, detect when ZMod m × ZMod n is cyclic, and show finite multiplicative subgroups of a field are cyclic."
 :terms [{:name "primary decomposition"
          :meaning "finite abelian group ≃ ⊕ cyclic p-power"
          :needed-because "solves part (a)"
         }
         {:name "order/lcm arithmetic"
          :meaning "order((a,b)) = lcm(order a, order b)"
          :needed-because "proves gcd(m,n)=1 iff cyclic"
         }
         {:name "root counting"
          :meaning "x^d−1 has ≤ d roots in a field"
          :needed-because "bounds the number of low-order elements in (c)"}]
 :strategy [{:id :s1
             :formal-dependency "Mathlib’s finite abelian classification"
             :informal-dependency "Stage 1(a)"
             :why-this-now "Part (a) is already in Mathlib"
             :lean-target "finiteAbelian_invariantFactors"
             :mathlib-status "available"}
            {:id :s2
             :formal-dependency "CRT + cyclic-order computations"
             :informal-dependency "Stage 1(b)"
             :why-this-now "Need to formalize gcd(m,n)=1 ↔ cyclic"
             :lean-target "zmod_prod_isCyclic_iff"
             :mathlib-status "missing"}
            {:id :s3
             :formal-dependency "roots-of-unity counting"
             :informal-dependency "Stage 1(c)"
             :why-this-now "Show finite multiplicative subgroups are cyclic"
             :lean-target "finite_mul_subgroup_cyclic"
             :mathlib-status "missing"}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1774995021497
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :summary "Opened the b94J01 frame."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the full algebraic solution in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded terms/strategies and formal targets in proof-plan and formal-alignment."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-blocked
  :summary "Lean work blocked: mathlib lacks `zmod_prod_isCyclic_iff` and a roots-of-unity counting lemma, so `finite_mul_subgroup_cyclic` cannot yet be implemented."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

(a) *Fundamental Theorem of Finite Abelian Groups.* Every finite abelian group `G` decomposes uniquely (up to ordering) as a direct product of cyclic p-power groups. Equivalently, there exist invariant factors `d₁ | d₂ | … | d_r` with `G ≅ ⊕_{i=1}^r ℤ/d_iℤ`.

(b) *When is ℤ/m ⊕ ℤ/n cyclic?* The direct sum is cyclic iff `gcd(m,n) = 1`. If `g = gcd(m,n) ≠ 1`, any element `(a,b)` has order dividing `lcm(m,n) = mn/g`, so no element reaches order `mn`. Conversely, when `gcd(m,n) = 1`, the element `(1,1)` has order `mn` (because `k(1,1)=0` implies `m|k` and `n|k`), so it generates the whole group.

(c) *Finite multiplicative subgroups are cyclic.* Let `G ⊆ Kˣ` be finite. For each divisor `d` of `|G|`, all elements whose order divides `d` are roots of `x^d - 1`, so there are at most `d` such elements. Since `∑_{d|n} φ(d) = n`, there must be an element whose order equals `|G|`, hence `G` is cyclic.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Primary decomposition** for finite abelian groups.
- **Order/lcm identities** to convert `gcd(m,n)=1` into the order of `(1,1)`.
- **Roots of unity counting**: in a field, `x^d - 1` has at most `d` roots.
- **Euler totient identity** `∑_{d|n} φ(d) = n` to finish part (c).

**Stage 3 — LEAN FORMALIZATION**

Targets:
- `finiteAbelian_invariantFactors` — cite Mathlib’s classification theorem (already present).
- `zmod_prod_isCyclic_iff (m n : ℕ)` — still missing, needs Chinese remainder input.
- `finite_mul_subgroup_cyclic (K : Type*) [Field K]` — not yet in mathlib; requires the roots-of-unity counting lemma.
All three pass the HtDP sanity check (they mention the real objects, avoid assuming the conclusion, and would be meaningful even without prose). However, mathlib currently lacks the CRT lemma “`ZMod m × ZMod n` cyclic iff `Nat.Coprime m n`” and the `x^d-1` counting API for arbitrary fields, so the Lean proofs remain blocked.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Once the CRT and root-counting lemmas land in mathlib, Stage 1 can cite the exact Lean theorem names. Until then, the textual argument stands on its own and Stage 3 records the open infrastructure work.
