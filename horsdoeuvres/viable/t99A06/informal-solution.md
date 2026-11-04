# APM t99A06: Euler characteristic obstructs a submersion to the circle

Assume, as is standard for this Euler-characteristic argument, that $X$ is a
compact oriented manifold without boundary. Suppose that
$f:X\to S^1$ were a submersion. Choose a Riemannian metric on $X$ and let $u$
be the nowhere-zero unit tangent vector field on $S^1$.

At each $x\in X$, the differential

$$
df_x:T_xX\longrightarrow T_{f(x)}S^1
$$

is surjective. Its restriction to the orthogonal complement of $\ker df_x$ is
an isomorphism. Define $V_x$ to be the unique vector in that complement such
that $df_x(V_x)=u_{f(x)}$. Smooth dependence of this inverse gives a smooth
vector field $V$ on $X$, and $V_x$ is never zero because its image is $u$.

The Poincaré--Hopf theorem says that the sum of the indices of the zeros of any
vector field with isolated zeros is $\chi(X)$. A nowhere-zero field has empty
zero set and hence total index zero. Therefore $\chi(X)=0$, contradicting the
hypothesis. No such submersion exists.

Compactness and the absence of boundary are essential to this formulation of
Poincaré--Hopf; if “manifold” in the source includes noncompact manifolds or
arbitrary boundary, the statement requires corresponding additional
hypotheses.
