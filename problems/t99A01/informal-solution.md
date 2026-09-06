# APM t99A01: Attaching cells of degrees 2, 4, and 5

Use the common CW structure with one vertex, one oriented 1-cell $a$, and one
2-cell for each attaching map. Van Kampen says that a degree-$d$ attaching map
adds the relation $a^d=1$. Hence

$$
\pi_1(X)=\langle a\mid a^2\rangle\cong\mathbb Z/2,
$$

$$
\pi_1(Y)=\langle a\mid a^2,a^4\rangle\cong\mathbb Z/2,
$$

and

$$
\pi_1(Z)=\langle a\mid a^2,a^4,a^5\rangle=1,
$$

because $\gcd(2,4,5)=1$.

The cellular chain complex has $C_0=\mathbb Z$, $C_1=\mathbb Z$, and
$C_2=\mathbb Z^r$, where $r=1,2,3$. The boundary $C_2\to C_1$ is respectively
the matrix $(2)$, $(2\ 4)$, or $(2\ 4\ 5)$; the boundary $C_1\to C_0$ is zero.
It follows that

$$
\begin{array}{c|ccc}
 &H_0&H_1&H_2\\ \hline
X&\mathbb Z&\mathbb Z/2&0\\
Y&\mathbb Z&\mathbb Z/2&\mathbb Z\\
Z&\mathbb Z&0&\mathbb Z^2.
\end{array}
$$

All higher homology groups vanish. For $Y$, the kernel of $(2\ 4)$ is generated
by $(-2,1)$. For $Z$, the map $(2\ 4\ 5):\mathbb Z^3\to\mathbb Z$ is
surjective and has a free kernel of rank two.
