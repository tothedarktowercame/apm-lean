# APM t99A04: Periods along separating and nonseparating curves

The printed statement says that $\eta$ is a form on an undefined space $F$;
the natural reading is that $\eta$ is a closed 1-form on $X$. There is also a
boundary ambiguity: the usual answer assumes that the compact oriented surface
$X$ is closed.

Under that standard assumption, if the embedded circle $C=f(S^1)$ separates
$X$, then it is the oriented boundary of the closure of one component of
$X\setminus C$. Stokes' theorem gives

$$
\int_{S^1}f^*\eta=\int_C\eta=\int_Md\eta=0.
$$

Thus the only possible value for a separating curve is zero.

For a nonseparating curve the answer changes. On the torus
$T^2=\mathbb R^2/\mathbb Z^2$, take $C$ to be the image of
$s\mapsto(s,0)$ and take $\eta=c\,dx$. Then $C$ is nonseparating, $\eta$ is
closed, and

$$
\int_C\eta=c.
$$

Since $c$ is arbitrary, every real value occurs. More conceptually, integration
is the de Rham pairing $H^1(X;\mathbb R)\times H_1(X;\mathbb R)\to\mathbb R$:
a separating curve is null-homologous, whereas a nonseparating simple closed
curve represents a nonzero homology class and admits a dual cohomology class.

If manifolds with boundary are literally allowed, “separating” alone does not
force zero: the core circle of an annulus separates it and $d\theta$ has a
nonzero period. Thus the source needs either “closed surface” or the weaker
condition $[C]=0$ for its expected first answer.
