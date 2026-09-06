# APM t99J05: Lefschetz computation for complex projective space

The formula is well-defined because multiplying $(z_0,z_1,z_2)$ by a nonzero
scalar multiplies $(z_0,2z_1,3z_2)$ by the same scalar. The homotopy

$$
H_s[z_0,z_1,z_2]=[z_0,(1+s)z_1,(1+2s)z_2],\qquad0\leq s\leq1,
$$

is well-defined at every time and joins the identity to $f$.

A fixed point must satisfy
$(z_0,2z_1,3z_2)=\lambda(z_0,z_1,z_2)$. Since the three eigenvalues are
distinct, only one coordinate can be nonzero. The fixed points are therefore

$$
[1,0,0],\qquad[0,1,0],\qquad[0,0,1].
$$

Near the eigenline for eigenvalue $\lambda_i$, affine complex coordinates in
the other two directions make the derivative diagonal with eigenvalues
$\lambda_j/\lambda_i$ for $j\ne i$. The real determinant defining the local
Lefschetz index is

$$
\det_{\mathbb R}(I-Df)=
\prod_{j\ne i}|1-\lambda_j/\lambda_i|^2>0.
$$

Hence each isolated fixed point has local index $+1$. The Lefschetz number is
their sum, namely $3$. Since $f$ is homotopic to the identity, its Lefschetz
number equals that of the identity, which is the Euler characteristic. Thus
$\chi(\mathbb{CP}^2)=3$.

For $\mathbb{CP}^n$, choose a projective linear map induced by a diagonal
matrix with $n+1$ distinct positive eigenvalues. It is homotopic to the
identity, its fixed points are precisely the $n+1$ coordinate lines, and the
same complex-coordinate determinant shows that every local index is $+1$.
Therefore

$$
\boxed{\chi(\mathbb{CP}^n)=n+1}.
$$
