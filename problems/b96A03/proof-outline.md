# Proof Outline: b96A03

The canonical Lean attempt proves the odd-order rational-purity assertion and
that the polynomial automorphisms preserve primality. One sorry remains for
the invariant-ring descent implication.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b96A03.md`

## Formal progress

- `MulEquiv.irreducible_iff` proves preservation of primes.
- The orbit product is represented by a deduplicated `Finset.image`.
- `Multiset.prod_primes_dvd` avoids the unsuitable `Subsingleton Rˣ`
  assumption of `Finset.prod_primes_dvd`: it only requires that each
  associatedness class occur at most once.
- Closer hop 2 defines and proves `apmAssociateStabilizer G π`, the subgroup
  whose elements carry `π` to an associate. Closure is obtained directly from
  `Associated.map`, transitivity, and inverse transport.

## Remaining bridge

Extract the unique constant unit for each member of `apmAssociateStabilizer`
as a character into `Fˣ`, and use
`apmFPure` to trivialize it. This yields equality of associated orbit elements
and hence the `countP` uniqueness premise for `Multiset.prod_primes_dvd`.
Orbit reindexing and domain cancellation then prove invariance, universal
divisibility, and primality in `apmFixedRing G`.
