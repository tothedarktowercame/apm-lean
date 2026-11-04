# APM t99A05: Odd degree produces an odd intersection

Under the standard hypotheses implicit in the mod-2 degree (closed $Z$ and
$Y$, or a proper restriction $f|_Z$), the answer is **yes**.

Choose a regular value $y\in Y$ of both $f$ and $f|_Z$; transversality permits
such a choice. Put

$$
W=f^{-1}(y).
$$

Then $W$ is a smooth submanifold of codimension $\dim Y$, and it is compact
when $f$ is proper (in particular when $X$ is compact). Its intersection with
$Z$ is transverse and equals

$$
W\cap Z=(f|_Z)^{-1}(y).
$$

By the regular-value definition of degree modulo two,

$$
I_2(W,Z)=\#(f|_Z)^{-1}(y)\pmod2=\deg_2(f|_Z)\ne0.
$$

Equivalently, $W$ represents the Poincaré dual of the pullback of the point
class in $Y$, and pairing that class with $[Z]$ gives the mod-2 degree.

The printed question omits compactness/properness assumptions on $X$ and $f$.
Without one of them, a regular fiber need not be compact, so the requested
compact $W$ does not follow from the literal text. The argument above is the
intended theorem and records precisely where that hypothesis is used.
