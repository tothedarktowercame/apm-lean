# Blueprint for t96A05

## Triage

Verdict: **true and faithful**. No statement repair is needed.

The source's final goal is precisely that a nullhomotopic map from a closed
subset of a normal space into `ℝ² \ {0}` extends to the whole space. The Lean
statement retains normality of both `X` and `X × [0,1]`, closedness of `A`,
continuity, nullhomotopy, and the exact restriction equality. The proof below
uses the stronger and simpler covering/Tietze route, so the product-normality
assumption is unused but harmless.

I tested the standard degeneracies. If `A=∅`, the unique empty map extends by
any constant nonzero map; the target is inhabited. If `X=∅`, necessarily
`A=∅` and the conclusion is again immediate. Constant `f` has the constant
logarithm supplied by `Complex.log`. The nullhomotopy condition is essential:
the identity map from `S¹⊆D²` into the punctured plane has nonzero winding and
cannot extend over the disk.

There are no solve-loop, topology-ledger, or audit rows for this problem. The
necessary APIs are in Mathlib itself. The blueprint adds their direct imports
to the original import without changing the theorem.

## Coordinate definitions

`APMT96A05.toComplex` identifies a nonzero real pair with a nonzero complex
number using `Complex.equivRealProdCLM.symm`; `APMT96A05.ofComplex` is the
reverse coordinate map. Their left-inverse identity is proved in the file.
These definitions keep the main theorem's target literally unchanged while
allowing use of the complex exponential covering.

## Remaining lemmas

### `apm_t96A05_exists_complex_logarithm`

**Statement in words.** A nullhomotopic map `f : A → ℝ² \ {0}` has a
continuous complex logarithm `u`, so `exp (u a)` is the complex coordinate of
`f a` for every `a`.

**Why true.** Compose `f` and its nullhomotopy with the continuous coordinate
map `toComplex`. Unpack `hf` as a homotopy from `f` to a constant `z₀` and
reverse it, so the constant map is the time-zero slice. Lift that constant
slice through complex exponential using the constant value
`Complex.log z₀`; `Complex.exp_log z₀.property` verifies the lift. Apply
`Complex.isCoveringMap_exp.liftHomotopy` to the reversed homotopy. Restrict the
lift to time one. `IsCoveringMap.liftHomotopy_lifts` and the endpoint equation
of the reversed homotopy give the required exponential identity.

The lifting theorem works for an arbitrary parameter space `A`; no local
connectedness, nonemptiness, or normality of `A` is needed.

**Expected size.** 60–100 lines.

**Dependencies.** Coordinate definitions and Mathlib's covering homotopy API
only. Independent of Tietze extension.

**Truth check.** For a constant map with value `z₀`, take the constant lift
`log z₀`. For `A=∅`, the lifted continuous map is the unique empty function.
The exact names `Complex.isCoveringMap_exp`,
`IsCoveringMap.liftHomotopy`, `liftHomotopy_lifts`, and `Complex.exp_log` were
checked with `#check` under the blueprint imports.

### `apm_t96A05_extend_from_complex_logarithm`

**Statement in words.** If a continuous complex logarithm of `f` is supplied,
then `f` extends continuously over `X`.

**Why true.** Convert the logarithm `u : A → ℂ` to the pair-valued map
`Complex.equivRealProdCLM ∘ u : A → ℝ×ℝ`. The product has a
`TietzeExtension` instance, so
`ContinuousMap.exists_extension hA.isClosedEmbedding_subtypeVal` gives a
continuous pair-valued extension `U : X → ℝ×ℝ`. Convert `U` back to complex
coordinates and exponentiate. Complex exponential is continuous and never
zero, hence defines a continuous map into the registered punctured-plane
subtype. On `A`, the Tietze restriction equation and `hlift`, followed by
`ofComplex_toComplex`, prove equality with `f`.

There is no direct `TietzeExtension ℂ` instance in this Mathlib version; the
pair-coordinate conversion is intentional. `TietzeExtension (ℝ×ℝ)` was
checked by `#synth`, and `ContinuousMap.exists_extension` and
`Complex.continuous_exp` were checked with `#check`.

**Expected size.** 35–60 lines.

**Dependencies.** Coordinate definitions and the supplied `hlift` hypothesis.
It is independent of the proof of the preceding lemma and can be assigned in
parallel.

**Truth check.** If the logarithm is constant, Tietze may choose the same
constant extension and exponentiation recovers the constant map. For empty
`A`, Tietze extends the empty pair-valued function, and exponential still
ensures the result avoids zero everywhere.

## Assembly and dependency layers

The main theorem has no `sorry`: it supplies
`apm_t96A05_exists_complex_logarithm` directly to
`apm_t96A05_extend_from_complex_logarithm`.

* **Layer 1 (parallel):** `apm_t96A05_exists_complex_logarithm` and
  `apm_t96A05_extend_from_complex_logarithm` (the latter takes the lift's
  conclusion as an explicit hypothesis).
* **Layer 2 (already compiled):** one-line assembly of `apm_t96a05`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96A05/Blueprint.lean
```

The two warnings identify exactly the two Layer 1 lemmas. The output of
`#print axioms apm_t96a05` is:

```text
'apm_t96a05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the registered theorem only through the two named
blueprint lemmas; the coordinate adapter and final assembly are sorry-free.
