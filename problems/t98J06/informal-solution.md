# Informal solution

At a fixed point (p),
\[
dF_p(v)=(v,df_pv),\qquad T_{(p,p)}\Delta=\{(u,u):u\in T_pX\}.
\]
Transversality says that these two subspaces span
\(T_pX\oplus T_pX\). Passing to the quotient by the diagonal identifies
the induced map with (v\mapsto df_pv-v\). Hence (df_p-I) is surjective,
and because its domain and codomain both have dimension (n), it is an
isomorphism.

Orient the normal bundle of the diagonal using the quotient isomorphism
\((a,b)\mapsto b-a\). The local intersection number of the graph of (f)
with the diagonal is the local degree of the resulting normal map
\(v\mapsto(df_p-I)v\). Since this derivative is nonsingular, that degree is
the sign of its determinant: (+1) when (df_p-I) preserves orientation
and (-1) when it reverses orientation.
