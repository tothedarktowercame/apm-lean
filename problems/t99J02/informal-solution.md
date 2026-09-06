# APM t99J02: The double torus

Let $X$ be the closed orientable surface of genus two.

## CW calculation

Use one 0-cell, four oriented 1-cells $a_1,b_1,a_2,b_2$, and one 2-cell
attached by the word

$$
[a_1,b_1][a_2,b_2].
$$

The cellular boundary $C_1\to C_0$ is zero. The boundary of the 2-cell is also
zero after abelianization because every generator occurs once with each sign.
Thus the cellular chain complex is

$$
0\longrightarrow\mathbb Z\xrightarrow{0}\mathbb Z^4
\xrightarrow{0}\mathbb Z\longrightarrow0,
$$

and

$$
H_0(X)=\mathbb Z,\qquad H_1(X)=\mathbb Z^4,\qquad
H_2(X)=\mathbb Z,
$$

with all other groups zero.

## Connected-sum calculation

Write $X=T^2\#T^2$ and cover it by the two punctured tori together with a
collar of the gluing circle. Van Kampen starts with two free groups
$\langle a_1,b_1\rangle$ and $\langle a_2,b_2\rangle$ and identifies their
boundary loops with opposite orientations. This gives

$$
\pi_1(X)=
\langle a_1,b_1,a_2,b_2\mid [a_1,b_1][a_2,b_2]=1\rangle.
$$

For Mayer--Vietoris, the intersection retracts to $S^1$. Its $H_1$ generator
maps to the boundary class in each punctured torus, which is zero in their
abelianized first homology. Exactness therefore gives $H_1(X)\cong\mathbb Z^4$.
The kernel at the intersection's $H_1\cong\mathbb Z$ supplies the fundamental
class $H_2(X)\cong\mathbb Z$, and connectedness gives $H_0(X)=\mathbb Z$.
Thus both requested computations agree.
