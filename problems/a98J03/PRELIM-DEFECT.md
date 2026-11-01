# Preliminary statement defect: a98J03

## Exact failing claim

The problem prints

\[
g_y(x)=\frac{y}{\pi}\int_{-\infty}^{\infty}
  \frac{1}{(x-t)+y^2}f(t)\,dt \qquad (y>0),
\]

and then claims that every such `g_y` is in `L^2(R)`, that `f \mapsto g_y`
is a family of bounded linear operators on `L^2(R)`, and that `g_y \to f` in
`L^2(R)` as `y \to 0`.

## Counterexample

Let `y = 1` and `f = 1_[0,1]`, which belongs to `L^2(R)`.  For every
`x in (-1,0)`, the alleged defining integral reduces to

\[
\int_0^1 \frac{dt}{x-t+1},
\]

whose pole `t = x+1` lies strictly inside `(0,1)`.  On the two sides of that
pole its positive and negative parts both have logarithmically divergent
integrals.  Thus the integrand is not Lebesgue integrable for every `x` in the
positive-measure set `(-1,0)`.  The displayed formula therefore does not
define `g_1` as an almost-everywhere finite Lebesgue integral, so clause (a)
already fails; consequently it cannot define the operators in (b), and the
convergence assertion in (c) is not a valid assertion about those `g_y`.

## Evident intent and smallest correction

This is the standard Poisson kernel for the upper half-plane.  Its denominator
is `((x-t)^2 + y^2)`: that square removes the moving real pole, makes the
kernel nonnegative with integral one, and gives the usual `L^2` contraction
and approximate-identity theorem.  The smallest correction is therefore only

\[
(x-t)+y^2 \quad\longmapsto\quad (x-t)^2+y^2.
\]

The source does not restrict scalars, so the Lean reformulation uses
complex-valued `L^2(R)`.  It keeps Lebesgue measurability through `MemLp`, with
no Borel strengthening.  After the denominator correction, all three clauses
stand as printed: membership in `L^2`, a family of bounded linear operators,
and `L^2` convergence to `f` as `y \to 0+`.
