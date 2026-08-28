# Fundamental groups of products

`fundamentalGroupProdMulEquiv` proves

```lean
FundamentalGroup (X × Y) (x, y) ≃*
  FundamentalGroup X x × FundamentalGroup Y y
```

directly from Mathlib's product and projection operations on homotopy classes
of paths.  Its two simp lemmas expose both directions: coordinate projection
and product of based loop classes.

The repository does not yet contain an axiom-clean computation
`FundamentalGroup Circle 1 ≃* Multiplicative ℤ`.  Consequently this module
does not claim the concrete torus computation; that circle theorem is the
next independent prerequisite.
