# Informal solution

The rotation (f:S^2\to S^2) is orientation preserving and has degree (1),
so its Lefschetz number is
\(L(f)=\operatorname{tr}(f_*|H_0)+\operatorname{tr}(f_*|H_2)=1+1=2\).
The reflection (g:S^1\to S^1) has degree (-1), hence
\(L(g)=1-(-1)=2\). By the Künneth theorem and multiplicativity of Lefschetz
numbers under products,
\[
 L(h)=L(f)L(g)L(g)=2\cdot2\cdot2=8.
\]

The map is not homotopic to the identity. For example, on the (H_1) summand
coming from either circle, (h_*) is multiplication by (-1), whereas the
identity induces (+1). Homotopic maps induce the same homomorphism on
homology, so no such homotopy can exist.
