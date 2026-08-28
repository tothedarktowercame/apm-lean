# Boundary-torus Mayer–Vietoris signed-fold algebra

For an object `Z` of any abelian category, `signedFold Z` is the composite

```
Z ⨞ Z --(1,1)--> Z --(1,-1)--> Z ⨞ Z,
```

so its two projections are the codiagonal and its negative.  In integer
coordinates it is `(a,b) ↦ (a+b,-a-b)`.

The target proves directly from biproduct universal properties that
`signedDiagonal Z : Z ⟶ Z ⨞ Z` is a kernel of `signedFold Z`, and that
`codiagonal Z : Z ⨞ Z ⟶ Z` is its cokernel.  It packages normalized
canonical isomorphisms

```
kernel (signedFold Z) ≅ Z
cokernel (signedFold Z) ≅ Z
```

and exactness of both consecutive triples. For `Z = AddCommGrpCat.of ℤ`,
the kernel coordinate is `a ↦ (a,-a)` and the quotient coordinate is the
sum of the two target coordinates.

No topological-sum comparison, Mayer–Vietoris map identification, torus
homology, or Künneth theorem is assumed. Generic extraction of a middle
homology object from a longer exact sequence remains consumer-specific until
the adjacent arrows and zero objects are supplied.
