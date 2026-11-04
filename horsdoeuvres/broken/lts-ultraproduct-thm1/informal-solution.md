# Informal solution

Let (q_i:A_i\to A_i/\sigma_i) be the quotient homomorphisms. They induce a
homomorphism
\[
 \Phi:\prod_{\mathcal D}A_i\longrightarrow
       \prod_{\mathcal D}(A_i/\sigma_i),\qquad
 [a_i]_{\mathcal D}\longmapsto[q_i(a_i)]_{\mathcal D}.
\]
It is well defined because equality of (a_i,b_i) on a
\(\mathcal D\)-large set implies equality of their quotient classes there,
and it preserves every basic operation coordinatewise.

The map is surjective: choose, for every coordinate, a representative in
\(A_i) of a given class in (A_i/\sigma_i) (choice is used here). Its kernel
congruence is exactly the ultraproduct congruence:
\[
 \Phi([a_i])=\Phi([b_i])
 \iff \{i:q_i(a_i)=q_i(b_i)\}\in\mathcal D
 \iff \{i:(a_i,b_i)\in\sigma_i\}\in\mathcal D.
\]
The first isomorphism theorem for algebras therefore factors (Phi) through
an isomorphism
\[
 \left(\prod_{\mathcal D}A_i\right)Big/
 \left(\prod_{\mathcal D}\sigma_i\right)
 \cong \prod_{\mathcal D}(A_i/\sigma_i),
\]
as claimed.
