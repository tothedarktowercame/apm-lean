<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94A07: A 180° rotation of the torus — four fixed points and a Lefschetz obstruction

## Why It's Hard

The map `f` is a rigid `180^\circ` rotation about the `x`-axis, and the task mixes a *geometric* count
(where are the fixed points?) with two *invariant-theoretic* computations (local Lefschetz indices, and
homotopy class). The fixed points are not obvious until you realize they are exactly where the **rotation
axis pierces the surface**, and one must then compute the derivative `df_p` on each tangent plane — which
requires identifying that tangent plane correctly. Part (b) is a trap if approached by trying to build or
rule out a homotopy directly; the clean route is the **Lefschetz number** as a homotopy invariant, and the
striking fact is that `L(f) = 4 \ne 0 = \chi(T) = L(\mathrm{id})`, which obstructs `f \simeq \mathrm{id}`
despite `f` being an honest diffeomorphism of the torus.

## The Key Insight

Place the donut as the tube of radius `r` around the circle `\{x^2+y^2 = R^2,\ z=0\}` (`R > r`). The rotation
is `f(x,y,z) = (x, -y, -z)`.

- **(a)** Fixed points satisfy `y = z = 0`: the `x`-axis meets `T` in **four** points
  `(\pm(R+r), 0, 0)` and `(\pm(R-r), 0, 0)`. At each, the tangent plane is the `yz`-plane, and `f` restricted
  to it is rotation by `180^\circ`, i.e. `df_p = -I`. Then `+1` is not an eigenvalue (so each is a
  **nondegenerate / Lefschetz** fixed point) and the local index is
  `\operatorname{sign}\det(I - df_p) = \operatorname{sign}\det(2I) = +1`.
- **(b)** Summing, `L(f) = 4`. (Independently: `f_* = -I` on `H_1(T) = \mathbb Z^2`, giving
  `L(f) = 1 - (-2) + 1 = 4`.) Since `L(\mathrm{id}) = \chi(T) = 0 \ne 4 = L(f)` and the Lefschetz number is a
  homotopy invariant, `f` is **not** homotopic to the identity.

## Complete Proof

Model `T` as the surface of revolution: the tube of radius `r` about the central circle
`\{x^2+y^2=R^2,\ z=0\}` in the `xy`-plane, with `R > r`. Rotation by `180^\circ` about the `x`-axis is the
linear isometry

$$f(x,y,z) = (x, -y, -z),$$

which maps `T` to `T` (it preserves the central circle and is a rigid motion).

### (a) Fixed points, Lefschetz property, local indices

**Count.** `f(p) = p \iff (x,-y,-z) = (x,y,z) \iff y = 0,\ z = 0`. So the fixed set is `T \cap (x\text{-axis})`.
A point `(x,0,0)` lies on `T` iff its distance to the central circle is `r`; the nearest central-circle
point to `(x,0,0)` is `(\pm R, 0, 0)`, at distance `\big||x| - R\big|`, so `(x,0,0) \in T \iff |x| = R \pm r`.
Hence the **four** fixed points

$$(R+r,0,0),\quad (R-r,0,0),\quad (-(R-r),0,0),\quad (-(R+r),0,0)$$

— the points where the `x`-axis punctures the torus (the outer and inner equatorial points on each side).

**Derivative at a fixed point.** At each of these points the tangent plane `T_pT` is the `yz`-plane:
moving along the toroidal direction (around the `z`-axis) is a `y`-displacement, and moving around the tube
(poloidal) is a `z`-displacement. Since `f` is linear, `df_p` is its linear part `\operatorname{diag}(1,-1,-1)`
restricted to `T_pT = \{x = \text{const}\}`-plane `= yz`-plane:

$$df_p = \operatorname{diag}(-1,-1) = -I \quad \text{on } T_pT.$$

(This is just "rotation by `180^\circ` in the plane `= -I`.")

**Lefschetz / nondegeneracy and local index.** The eigenvalues of `df_p = -I` are `-1, -1`, so `+1` is **not**
an eigenvalue: `\det(df_p - I) = \det(-2I) = 4 \ne 0`, hence each fixed point is a **nondegenerate (Lefschetz)
fixed point**. The local Lefschetz number (index) is

$$L_p(f) = \operatorname{sign}\det(I - df_p) = \operatorname{sign}\det(2I) = \operatorname{sign}(4) = +1.$$

So **all four** fixed points are Lefschetz, each with local Lefschetz number `+1`.

(Consistency: the global Lefschetz number is the sum of local indices, `L(f) = 4`. Check via homology:
`H_*(T) = (\mathbb Z, \mathbb Z^2, \mathbb Z)`; `f_*` is the identity on `H_0` and on `H_2` (`f` preserves
orientation, mapping the outward normal to the outward normal), and `f_* = -I` on `H_1 = \mathbb Z^2` (the
`180^\circ` rotation reverses both the toroidal loop `a` and the poloidal loop `b`). Thus
`L(f) = 1 - (-2) + 1 = 4`.)

### (b) `f` is not homotopic to the identity

The Lefschetz number is a homotopy invariant, and for the identity `L(\mathrm{id}) = \chi(T) = 2 - 2g = 0`.
If `f` were homotopic to `\mathrm{id}`, then `L(f) = L(\mathrm{id}) = 0`. But by part (a), `L(f) = 4 \ne 0`.
Therefore

$$\boxed{\ f \text{ is not homotopic to the identity.}\ }$$

(Equivalently and more directly: homotopic maps induce the same map on homology, but `f_* = -I \ne I = \mathrm{id}_*`
on `H_1(T) = \mathbb Z^2` — since `-1 \ne 1` in `\mathbb Z` — so `f \not\simeq \mathrm{id}`.) ∎

**Remark.** The geometry and the algebra reinforce each other. Geometrically, a `180^\circ` rotation about an
axis that *pierces* a surface fixes exactly the piercing points and acts as `-I` on each tangent plane (a
half-turn), so every fixed point is automatically nondegenerate with index `+1`; the count `4` is the number
of times the `x`-axis crosses the torus. Algebraically, `L(f) = \sum_p L_p(f) = 4`, while the identity has
`L = \chi(T) = 0` — the gap `4 \ne 0` is the homotopy obstruction. The underlying reason `f \not\simeq \mathrm{id}`
is that `f` *flips* the torus, reversing both homology generators (`f_* = -I` on `H_1`), something no
deformation of the identity can do.
