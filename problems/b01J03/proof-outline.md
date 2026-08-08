# Proof Outline: b01J03

The canonical attempt is `lean/Main.lean`; its main theorem has one remaining
`sorry`.

## Proved in closer hop 3

`apm_b01J03_selfNormalizer_count` packages the Sylow normalizer calculation:
for a finite group and self-normalizing Sylow `P`,
`Nat.card (Sylow p G) = P.index` and `p ∤ P.index`. It uses the previously
missed Mathlib theorems `Sylow.card_eq_index_normalizer` and
`Sylow.not_dvd_index`.

## Remaining route

1. Construct the faithful action of `K ≃ₐ[F] K` on the `p` distinct roots.
   This shows the group cardinal divides `p!`; transitivity shows `p` divides
   it, hence its `p`-multiplicity is exactly one.
2. Set `s = P.index`, use `Subgroup.card_mul_index` and
   `Sylow.card_eq_multiplicity` to prove `|G| = p*s`.
3. Partition order-`p` elements among the `s` Sylow subgroups to obtain
   `s*(p-1)`.
4. Use `IsGalois.card_fixingSubgroup_eq_finrank`, adjoin/minpoly finrank, and
   the order-`p` count to identify all root stabilizers.
5. Use the splitting-field generation property to show every root lies in
   `F[α]`, hence `F[α]=K`, `s=1`, and `P=⊤`.

The faithful root action and the finite partition in steps 1 and 3 are the
largest missing formal bridges.

## Hop 4: exact missing Mathlib-level contract

No packaged finite-union theorem was found after searching the repository
index, all construction modules, and Mathlib's Sylow, p-group, cyclic-group,
and order-of-element developments. The exact reusable statement needed for
step 3 is:

```lean
theorem apm_b01J03_card_orderOf_eq_prime
    (G : Type*) [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime)
    (hPcard : ∀ P : Sylow p G, Nat.card P = p) :
    Nat.card {g : G // orderOf g = p} =
      Nat.card (Sylow p G) * (p - 1)
```

Every order-`p` element generates a subgroup contained in a Sylow subgroup;
under `hPcard`, two such Sylow subgroups meeting away from `1` coincide, and
each contributes exactly `p - 1` nonidentity elements. Existing declarations
provide these local facts but not their finite disjoint-union assembly.
