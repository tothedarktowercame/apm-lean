# Blueprint for t00J03

## Triage

Verdict: **true and faithful**. No further statement repair is needed.

The source describes the angle form on `ℝ² \ {0}`, its descent to `ℝP¹`,
and its integral with orientation discussed. The registered statement models
the projective line by Mathlib's actual `Projectivization`, models tangent
representatives by a quotient allowing both nonzero rescaling and addition of
a radial vector, and asks for one traversal by the projected half-circle. It
states `+π` for increasing angle and `-π` for the reversed traversal.

I tried the main degeneracies. The punctured-plane subtype rules out the zero
vector, so the form's denominator cannot vanish. Negative scaling is included
in the quotient relation, so the antipodal endpoint identification is not
lost. The domain `Ico 0 π` contains exactly one of the equal endpoints; using
`Icc` would destroy injectivity, while using `Ioo` would miss the horizontal
line. Finally `π > 0`, so the half-open domain is nonempty and the two
orientations really give opposite nonzero values.

There are no solve-loop or topology-ledger rows for this problem. The existing
proof in `Main.lean` already establishes all algebraic work: representative
invariance (`apm_t00j03_angleFormValue_change`), descent by `Quotient.lift`,
the constant value one along the half-circle, and the two oriented integrals.
Those proofs are copied unchanged into the blueprint. Only the topology of the
explicit projective loop remains admitted.

## Remaining lemmas

### `apm_t00j03_projectiveLoop_continuous`

**Statement in words.** The map sending an angle to the projective class of
`(cos θ, sin θ)` is continuous on all of `ℝ`.

**Why true.** The coordinate map is continuous by `Real.continuous_cos` and
`Real.continuous_sin`. Package it into the punctured-plane subtype using the
already proved nonvanishing argument in `apm_t00j03_circlePoint`, then compose
with the quotient map. The exact quotient API is
`continuous_quotient_mk'`; `apm_t00j03_projectivize` is definitionally that
map after the subtype/projectivization abbreviations are unfolded.

**Expected size.** 30–60 lines.

**Dependencies.** Definitions only; independent of the fundamental-domain
lemma.

**Truth check.** At `θ = 0` and `θ = π`, the chosen vectors differ by the
continuous antipodal motion and their quotient values agree. Thus there is no
endpoint discontinuity hidden by the projective quotient. The cited API names
were checked with `#check` in the compiling blueprint environment.

### `apm_t00j03_projectiveLoop_fundamentalDomain`

**Statement in words.** Every real projective line has exactly one angle in
`[0,π)`, and the angles `0` and `π` project to the same line.

**Why true.** For surjectivity, take `p.rep = (x,y) ≠ 0`, normalize it to the
unit circle, and choose its polar angle modulo `π`, moving `π` to `0` when
necessary. `Projectivization.mk_rep` identifies this normalized vector's
class with `p`. For injectivity, use
`Projectivization.mk_eq_mk_iff'`: equality of the two projective classes gives
a scalar `a` relating the two unit vectors. Norms force `a² = 1`, hence
`a = 1` or `a = -1`. The first case gives equal sine and cosine and hence
equal angles within `[0,π)`; the second would make the angle difference `π`,
which is impossible for two members of the half-open interval. For the
endpoint equality, apply the same projectivization criterion with scalar
`-1`, then simplify `sin 0`, `cos 0`, `sin π`, and `cos π`.

If polar-angle extraction is awkward, an equivalent route splits on the sign
of `y`, uses `Real.arccos (x / ‖(x,y)‖)` to choose an angle in `[0,π]`, and
resolves the sole `π` endpoint by antipodal rescaling. The identities rest on
`Real.sin_sq_add_cos_sq`.

**Expected size.** 100–150 lines.

**Dependencies.** Definitions only; independent of continuity and of the
form-descent calculation.

**Truth check.** The coordinate axes give the boundary cases: `[1:0]` uses
angle `0`, `[-1:0]` would use `π` but is rescaled to angle `0`, and `[0:1]`
uses `π/2`. Two angles in `[0,π)` differing by an antipodal half-turn cannot
both remain in that interval. The exact equality API
`Projectivization.mk_eq_mk_iff'` was checked with `#check`.

## Reused completed work and assembly

`apm_t00j03_previous_encoding` is a complete, sorry-free proof that the form
descends and that its positive and reversed integrals are `π` and `-π`. It
uses the already compiled `angleFormValue_change`, `Relation.EqvGen.rec`, and
the two interval-integral lemmas. The final theorem simply combines that
result with the two topology lemmas and contains no `sorry`.

## Dependency layers

* **Layer 1 (parallel):**
  `apm_t00j03_projectiveLoop_continuous` and
  `apm_t00j03_projectiveLoop_fundamentalDomain`.
* **Layer 2 (already compiled, no seat needed):** assemble the two topology
  conclusions with `apm_t00j03_previous_encoding` to prove `apm_t00j03`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00J03/Blueprint.lean
```

The two warnings identify exactly the two Layer 1 lemmas. The output of
`#print axioms apm_t00j03` is:

```text
'apm_t00j03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the main theorem only through the two named topology
lemmas. The descent, integral evaluation, and final assembly are sorry-free.
