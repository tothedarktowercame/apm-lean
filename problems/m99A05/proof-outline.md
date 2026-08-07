# Proof Outline: m99A05

The proof is complete.

1. The standard basis of complex `ℓ²` converges weakly to zero because every
   representing `ℓ²` sequence has coordinates tending to zero, but its norms
   remain one.
2. Strong convergence implies weak convergence by continuity of every bounded
   linear functional.
3. In finite dimension, `Module.finBasis` gives a continuous linear equivalence
   with a finite coordinate space. Weak convergence supplies convergence of
   every coordinate, and the inverse equivalence recovers norm convergence.
4. Weak convergence makes the canonical bidual images pointwise bounded.
   `banach_steinhaus` bounds their operator norms, which equal the original
   vector norms by the isometric bidual embedding.
5. Hahn–Banach separation gives uniqueness of weak limits.
