import Mathlib

noncomputable section

/-!
# APM b01A02

## Statement repairs

None.

## Encoding notes

The order and subgroup index are the actual finite cardinality and
`Subgroup.index`. Normality and cyclicity use Mathlib's structural predicates,
rather than merely asserting numerical consequences of them.
-/

def apmSmallestPrimeDivisor (p n : ℕ) : Prop :=
  p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q

theorem apm_b01a02 :
    (∀ (G : Type*) [Group G] [Fintype G]
      (p : ℕ) (H : Subgroup G),
      apmSmallestPrimeDivisor p (Fintype.card G) →
      H.index = p → H.Normal) ∧
    (∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G = 255 →
        (∃ P : Subgroup G, P.Normal ∧ Nat.card P = 17) ∧
        (∃ H : Subgroup G,
          H.Normal ∧ Nat.card H = 85 ∧ IsCyclic H) ∧
        IsCyclic G) := by
  -- SKIPPED: two-part finite group theory.
  -- (a) Subgroup of index p (smallest prime divisor of |G|) is normal:
  --     action of G on G/H gives homomorphism G → S_p; kernel ⊆ H;
  --     |G/Ker| divides p! and |G|, forcing |G/Ker| | p, hence H=Ker is normal.
  -- (b) Groups of order 255=3·5·17 are cyclic:
  --     Sylow theorems: n_17=1 (normal subgroup of order 17),
  --     n_5|51, n_5≡1(mod 5) → n_5=1 or 51; n_3|85, n_3≡1(mod 3) → n_3=1 or 85;
  --     counting argument shows at least one of n_3=1 or n_5=1;
  --     normal subgroup of order 85 is cyclic (gcd(5,17)=1);
  --     quotient by it has order 3, etc.
  -- Blocker: requires Sylow theorems (NOT in Mathlib as ready-to-use),
  -- group actions on cosets, counting arguments.
  -- APIs: `Subgroup.index`, `Subgroup.Normal`, `Sylow` — Sylow theory absent.
  sorry
