# APM tunk01: Classification of the polygon surface

The word contains fourteen sides and seven edge labels $a,b,c,d,e,f,g$, each
appearing twice. Thus the quotient has one 2-cell and seven 1-cells. The
problem states that the corners form exactly two vertex classes, so its Euler
characteristic is

$$
\chi=V-E+F=2-7+1=-4.
$$

The surface is nonorientable: for example, the two occurrences of $a$ have the
same orientation. In an orientable polygon presentation every paired label
would occur once with each exponent. The classification theorem for closed
surfaces says that a nonorientable surface is
$N_k=\#^k\mathbb{RP}^2$, with $\chi(N_k)=2-k$. Therefore

$$
2-k=-4,
$$

so $k=6$. The polygon represents

$$
\boxed{N_6=\#^6\mathbb{RP}^2}.
$$

This agrees with the duplicate exercise `t94J09`. An older cut-and-paste note
claimed three projective planes, but that would have Euler characteristic
$-1$ and contradicts the explicitly supplied count of two vertex classes.
