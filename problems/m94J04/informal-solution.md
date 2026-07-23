<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94J04: Distributional curl of a discontinuous field — tangential jumps make no surface delta

## Why It's Hard

The vector field `u = f\,e_1` has a **discontinuous** component, so one's reflex is to expect the curl
to contain a singular "surface delta" supported on the discontinuity, the way `H'(x) = \delta(x)`. The
real content is learning *when* such a delta actually appears and when it does not — and the answer
turns on a subtle geometric fact: a jump of `f` across a surface contributes a delta only to the
derivatives taken in the **normal** direction of that surface, not to the tangential ones. Because the
curl of `(f,0,0)` uses only `\partial_y f` and `\partial_z f`, a jump across a plane `\{x = \text{const}\}`
(normal `e_1`) produces *no* singular term, even though `f` is genuinely discontinuous there.

There is also a wrinkle in the problem statement itself: as written, "`f = y` if `x>0` and `f = x` if
`z<0`" is **not well defined** — the two regions overlap (where `x>0` and `z<0`, `f` would be both `y`
and `x`) and together miss the region `\{x\le 0,\ z\ge 0\}`. The well-posed reading, used here, is the
partition `f = y` for `x>0` and `f = x` for `x<0` (i.e. a single jump across the plane `x=0`); the
distributional principle below also tells you exactly what changes if the jump were instead across
`z=0`.

## The Key Insight

For `u = (f,0,0)`, the curl is

$$\nabla \times u = (\partial_y u_3 - \partial_z u_2,\ \partial_z u_1 - \partial_x u_3,\ \partial_x u_2 - \partial_y u_1)
= (0,\ \partial_z f,\ -\partial_y f).$$

**Only `\partial_y f` and `\partial_z f` enter — never `\partial_x f`.** Now the distributional gradient of
a function jumping by `[f]` across a surface `S` with unit normal `n` is

$$\nabla f = \{\nabla f\} + [f]\,n\,\delta_S,$$

where `\{\nabla f\}` is the classical (a.e.) gradient. So the singular part of `\partial_i f` is
`[f]\,n_i\,\delta_S`. For a jump across `\{x=0\}`, `n = e_1 = (1,0,0)`, hence `n_y = n_z = 0`: the
singular parts of `\partial_y f` and `\partial_z f` **vanish**. The jump lives in the one derivative
(`\partial_x f`) that the curl does not see. Consequently `\nabla \times u` is a regular distribution,
equal to its classical value with no delta. (Had `f` jumped across `\{z=0\}`, with `n = e_3`, the term
`[f]\delta(z)` would appear in `\partial_z f` and hence in the `e_2`-component — see the remark.)

## Complete Proof

Take the well-posed reading `f(x,y,z) = y` for `x>0` and `f(x,y,z) = x` for `x<0`, and
`u = f\,e_1 = (f,0,0)`. Write the Heaviside function `H(x)` (`=1` for `x>0`, `=0` for `x<0`). Then

$$f = H(x)\,y + \big(1 - H(x)\big)\,x = x + H(x)\,(y - x). \tag{1}$$

`f` is locally integrable, so it is a distribution and `u` has a distributional curl.

**Step 1 — The curl uses only `\partial_y f, \partial_z f`.** Since `u_2 = u_3 = 0`,

$$\nabla \times u = \big(0,\ \partial_z f,\ -\partial_y f\big). \tag{2}$$

**Step 2 — Compute the two tangential derivatives distributionally.** From (1):

- `\partial_z f = 0`, because `f` does not depend on `z`.
- `\partial_y f = \partial_y\big[x + H(x)(y-x)\big] = H(x)\,\partial_y(y - x) = H(x)`. The factor `H(x)`
  is untouched by `\partial_y`, and no `\delta` arises because `\partial_y` differentiates *along* the
  plane of discontinuity `\{x=0\}`.

**Step 3 — Assemble.** Substituting into (2),

$$\boxed{\ \nabla \times u = \big(0,\ 0,\ -H(x)\big) = -H(x)\,e_3.\ }$$

Explicitly, `\nabla \times u = (0,0,-1)` for `x > 0` and `\nabla \times u = 0` for `x < 0`. It is a
**regular** distribution (an ordinary, if discontinuous, function): there is **no** surface-delta term,
despite `f` jumping by `[f] = y` across `\{x = 0\}`.

**Why no delta — the consistency check.** The jump *does* produce a singular term, but only in the
normal derivative `\partial_x f`, which the curl never uses:

$$\partial_x f = \partial_x\big[x + H(x)(y-x)\big] = 1 + \delta(x)(y - x) + H(x)(-1)
= \big(1 - H(x)\big) + y\,\delta(x),$$

using `(y-x)\delta(x) = y\,\delta(x)`. The `y\,\delta(x)` is the surface delta on `\{x=0\}`. In the curl
of `(f,0,0)` this `\partial_x f` enters only through `u_3` and `u_2`, both of which are zero — so the
delta is annihilated. ∎

**Remark (the statement's ambiguity, and the case that *does* give a delta).** As literally printed the
definition is inconsistent; the computation above takes the natural single-jump-across-`x=0` repair. The
general principle of Step 2 lets you handle any variant: if instead `f` jumps across `\{z=0\}` — for
example `f = y` for `z>0` and `f = x` for `z<0`, i.e. `f = x + H(z)(y-x)` — then `\partial_y f = H(z)`
(no delta) but

$$\partial_z f = (y - x)\,\delta(z) = (y - x)\,\delta(z),$$

so `\nabla \times u = \big(0,\ (y-x)\,\delta(z),\ -H(z)\big)` now carries a genuine surface delta on the
plane `z=0` in its `e_2`-component. The contrast between the two cases is exactly the lesson: a jump
contributes to `\nabla \times (f\,e_1)` if and only if the discontinuity surface has a normal with a
`y`- or `z`-component; a jump across a plane normal to `e_1` is invisible to this curl.
