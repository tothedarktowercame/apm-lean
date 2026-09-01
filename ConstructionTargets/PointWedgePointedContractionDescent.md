# Point-wedge pointed contraction descent

`wedgeHomotopyEquivLeft` says that wedging an arbitrary space `X` with a
pointedly contractible space `Y` does not change the homotopy type: the
orientation is

```lean
PointWedgeQuotient.Wedge x₀ y₀ ≃ₕ X
```

The forward map is the quotient-descended collapse which is the identity on
left representatives and sends every right representative to `x₀`.  Its
inverse is the canonical left inclusion.

The homotopy keeps the left summand fixed and applies the supplied pointed
contraction on the right summand.  The equation `h.fixed` is what makes this
map respect the generating identification between the two wedge points at
every time.  Continuity is proved jointly in time and the quotient variable
using the quotient-map product lifting property.

The two representative formulas are exposed as simp theorems.  This target is
generic in both spaces and both chosen points; it does not construct wedge
open covers or perform any fundamental-group or homology calculation.
