# Informal solution

For each (x\in X), surjectivity of (df_x:T_xX\to T_{f(x)}Y) gives a
neighborhood (U_x) and a smooth local right inverse of (df); applying it
to (v\circ f) gives a local lift (w_x). Choose a locally finite partition
of unity \(\{\rho_i\}\) subordinate to such neighborhoods and put
\(w=\sum_i\rho_iw_i\). Then
\[
df(w)=\sum_i\rho_i,df(w_i)=\sum_i\rho_i(v\circ f)=v\circ f.
\]
(Equivalently, a Riemannian metric identifies a smooth horizontal complement
to \(\ker df\), on which (df) is an isomorphism.)

On (S^1), take the unit angular vector field (v), whose time-(t) flow is
rotation through (t). Lift it to (w) as above. Since (X) is compact,
the flow \(\Phi_t\) of (w) exists for all (t). Uniqueness for integral
curves and (df(w)=v\circ f) imply
\[
 f(\Phi_t(x))=R_t(f(x)).
\]
Therefore \(\Phi_\pi\) maps (f^{-1}(1,0)) onto (f^{-1}(-1,0)).
Its inverse is \(\Phi_{-\pi}\), so its restriction is the required
diffeomorphism.
