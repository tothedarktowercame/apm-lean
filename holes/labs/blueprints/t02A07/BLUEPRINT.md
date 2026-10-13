# Blueprint for t02A07

## Triage

Verdict: **true after the repair already recorded in `Main.lean`**. No new
statement repair is needed.

The raw source calls `X` the unit sphere but repeats `(x²)²` and omits
`(x¹)²`. The registered file uses the standard unit sphere in `ℝ⁴`, which is
the smallest correction warranted by that phrase and by the intended
solution. Its regular-derivative predicate encodes codimension two in ambient
`ℝ⁴`, hence dimension two, and its tangent-space equation is the concrete
transversality condition for the displayed slices.

I tried the relevant degeneracies. On `Z`, `x₂x₃=1/4`, so neither product
coordinate can vanish. If the sphere gradient `x` were parallel to
`(0,0,x₃,x₂)`, then `x₀=x₁=0` and either `x₂=x₃`, which gives norm squared
`1/2`, or `x₂=-x₃`, which makes the product nonpositive. Thus the constraints
are regular.

For a parameter `(λ,μ)`, intersection with `Z` is governed by
`λ² y₁y₂=1/4`. If `λ=0` there is no intersection, so transversality is
vacuous. At a genuine intersection, the derivative on the tangent plane of
`S²` can vanish only at `y₀=0` and `y₁=y₂=±1/√2`; its value is then `λ²/2`.
Consequently a slice is nontransverse exactly when `λ²=1/2`. This cuts out
four points of the parameter circle, whose complement is dense.

No consumer-specific solve-loop or useful topology-contract result exists.
The borrowed `t97J05` stop concerns unrelated downstream topology and does
not supply this finite-dimensional calculation. The existing sorry-free
coordinate nonvanishing, range-in-sphere, and ambient-family lemmas are copied
unchanged.

## Remaining lemmas

### `apm_t02A07_bridge_constraint_gradients_independent`

**Statement in words.** At every point of `Z`, the position vector and the
product-gradient vector `(0,0,x₃,x₂)` are linearly independent.

**Why true.** Expand linear independence for a two-element `Fin 2` family.
If `a x + b(0,0,x₃,x₂)=0`, use the last two coordinates together with
`x₂x₃=1/4`. Eliminating `a,b` shows that dependence would force the two
vectors parallel. The first two coordinates then vanish, while the final two
give either `x₂=x₃` or `x₂=-x₃`; the sphere norm and positive product exclude
both cases as in the triage calculation. The already proved
`apm_t02a07_product_coordinates_ne_zero` permits all necessary cancellations.

**Expected size.** 50–90 lines.

**Dependencies.** Definitions and the compiled coordinate-nonvanishing
lemma only.

**Truth check.** At the symmetric product point `x₂=x₃=1/2`, the product
gradient has final coordinates `(1/2,1/2)`, but the sphere equation forces a
nonzero first or second coordinate, immediately preventing parallelism. The
antisymmetric possibility contradicts the positive product.

### `apm_t02A07_constraints_fderiv_surjective`

**Statement in words.** Assuming the two explicit gradient rows are
independent everywhere on `Z`, the derivative of the frozen two-coordinate
constraint map is surjective there.

**Why true.** Compute the derivative coordinatewise.
`fderiv_norm_sq_apply` identifies the first coordinate as
`v ↦ 2⟪x,v⟫`; product and subtraction rules identify the second as
`v ↦ x₃v₂+x₂v₃`. Thus the adjoint sends the two standard basis vectors of
`ℝ²` to nonzero scalar multiples of the two vectors in `hind`. Independence
gives injectivity of the adjoint; in finite dimensions, injectivity of the
adjoint is equivalent to surjectivity of the original map. An equally direct
route constructs preimages using the Gram matrix, whose determinant is
nonzero by `hind`.

**Expected size.** 70–120 lines.

**Dependencies.** Definitions and the supplied `hind` hypothesis. It does not
depend on the proof of the preceding lemma and can be developed in parallel.

**Truth check.** The two output rows have rank two exactly when their gradient
vectors are independent. At a point with nonzero first coordinate, the first
row already sees that direction while the product row does not, making the
rank calculation transparent. `fderiv_norm_sq_apply` was checked in
`Mathlib.Analysis.InnerProductSpace.Calculus`.

### `apm_t02A07_transverse_iff_parameter_sq_ne_half`

**Statement in words.** The slice at `(λ,μ)` is transverse to `Z` exactly when
`λ² ≠ 1/2`.

**Why true.** Differentiate `familyAmbient` in the `S²` variable. Because the
family already lands in the sphere, transversality to `Z` reduces to the
product constraint having a nonzero derivative along the image of the sphere
tangent plane. Its pullback is

`h(y)=λ² y₁y₂`, with derivative `λ²(y₂v₁+y₁v₂)`.

This functional vanishes on `yᗮ` iff `(0,y₂,y₁)` is parallel to `y`. At an
intersection all of `λ,y₁,y₂` are nonzero, so the coordinate equations force
`y₀=0` and `y₁=y₂` (the opposite sign is incompatible with the positive level).
The sphere equation gives `y₁y₂=1/2`, and the level equation then gives
`λ²=1/2`. Conversely, when `λ²=1/2`, choose either of the two points with
`y₀=0`, `y₁=y₂=±1/√2`; the derivative vanishes on the tangent plane, so the
submodule supremum in `IsTransverse` is not top.

The proof must finally translate this scalar-functional criterion back to the
literal `Submodule.map ... ⊔ tangentZ = ⊤`; regularity of the constraints can
be established locally by the same explicit rows rather than depending on
the first two blueprint lemmas.

**Expected size.** 110–150 lines.

**Dependencies.** Definitions and compiled family/range facts only. It is
independent of regularity assembly and of parameter-space density.

**Truth check.** At `λ=0` the slice never meets `Z`, so both sides are true.
At `λ=1`, critical product values on `S²` are `±1/2`, not `1/4`, so the slice
is transverse. At `λ²=1/2`, the displayed symmetric points lie over level
`1/4` and are critical, giving exact failure.

### `apm_t02A07_good_parameters_dense`

**Statement in words.** Parameters on the unit circle satisfying
`λ² ≠ 1/2` form a dense subset.

**Why true.** Solve `λ²=1/2` together with `λ²+μ²=1`; both coordinates have
absolute value `1/√2`, so the bad set consists of four points. Show each
singleton has dense complement in the circle by rotating a point through
arbitrarily small nonzero angles, then intersect the four open dense
complements. Mathlib provides `dense_compl_singleton`; alternatively, the
explicit rotation directly proves every relative open ball contains a good
point and avoids any instance search for punctured neighborhoods.

**Expected size.** 40–80 lines.

**Dependencies.** Only the parameter-circle definition. Independent of all
derivative calculations.

**Truth check.** The four bad points are the sign choices
`(±1/√2,±1/√2)`. Every nontrivial arc contains infinitely many other points,
so deleting these four cannot remove an open arc.

## Assembly and dependency layers

`apm_t02A07_bridge_transverse_parameters_dense` is sorry-free: it rewrites
the classified transversality predicate and applies the good-parameter density
lemma. The main theorem is also sorry-free: regularity applies the derivative
lemma to the row-independence lemma, the range conjunct uses the already
proved `apm_t02a07_family_mem_X`, and density uses the assembled bridge.

* **Layer 1 (all parallel):** gradient independence, derivative surjectivity
  with `hind` supplied as a hypothesis, exceptional-parameter classification,
  and good-parameter density.
* **Layer 2 (already compiled):** density bridge and `apm_t02a07` assembly.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t02A07/Blueprint.lean
```

The four `sorry` warnings identify exactly the four Layer 1 lemmas. The output
of `#print axioms apm_t02a07` is:

```text
'apm_t02a07' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the theorem only through the named blueprint lemmas;
both assembly declarations are sorry-free.
