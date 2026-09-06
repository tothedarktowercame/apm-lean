# APM a94A02: Differentiating a series of monotone functions

Let $(f_n)$ be nondecreasing, absolutely continuous functions from $[0,1]$ to
$[0,\infty)$, and suppose

$$
\sum_{n=1}^{\infty}f_n(1)<\infty.
$$

Write

$$
f(x)=\sum_{n=1}^{\infty}f_n(x).
$$

Because $0\leq f_n(x)\leq f_n(1)$ on $[0,1]$, the Weierstrass test shows that
the series defining $f$ converges uniformly. In particular, $f$ is continuous
and nondecreasing.

## Part (a): Integrability and finiteness of the derivative sum

Each absolutely continuous $f_n$ is differentiable almost everywhere. There
are only countably many functions, so outside one null set all the $f_n$ are
differentiable simultaneously. Since every $f_n$ is nondecreasing,

$$
f_n'(x)\geq0
$$

wherever its derivative exists. Thus the function in the question agrees
almost everywhere with the nonnegative series

$$
g(x)=\sum_{n=1}^{\infty}f_n'(x).
$$

For an absolutely continuous function, the fundamental theorem of calculus
gives

$$
\int_0^1 f_n'(x)\,dx=f_n(1)-f_n(0).
$$

Tonelli's theorem applies to the nonnegative functions $f_n'$. Hence

$$
\begin{aligned}
\int_0^1 g(x)\,dx
 &=\sum_{n=1}^{\infty}\int_0^1 f_n'(x)\,dx\\
 &=\sum_{n=1}^{\infty}\bigl(f_n(1)-f_n(0)\bigr)\\
 &\leq\sum_{n=1}^{\infty}f_n(1)<\infty.
\end{aligned}
$$

Therefore $g$ is integrable. A nonnegative measurable function with finite
integral is finite almost everywhere, proving both assertions in part (a).

## Part (b): Identifying the derivative of the sum

Set

$$
c=\sum_{n=1}^{\infty}f_n(0),
$$

which is finite because $0\leq f_n(0)\leq f_n(1)$. Absolute continuity gives,
for every $n$ and every $x\in[0,1]$,

$$
f_n(x)=f_n(0)+\int_0^x f_n'(s)\,ds.
$$

Summing this identity and applying Tonelli once more yields

$$
\begin{aligned}
f(x)
 &=\sum_{n=1}^{\infty}f_n(0)
   +\sum_{n=1}^{\infty}\int_0^x f_n'(s)\,ds\\
 &=c+\int_0^x\sum_{n=1}^{\infty}f_n'(s)\,ds\\
 &=c+\int_0^x g(s)\,ds.
\end{aligned}
$$

The indefinite integral of an $L^1$ function is absolutely continuous and has
derivative equal to its integrand almost everywhere. It follows that

$$
f'(x)=g(x)
$$

for almost every $x\in[0,1]$, as required.

This also proves the hint's inequality $f'(x)\geq g(x)$ almost everywhere;
indeed, equality holds.

## Relation to the Lean proof

The formal proof extends every $f_n$ constantly outside $[0,1]$ by composing
with the monotone clamp $x\mapsto\max(0,\min(1,x))$. It then applies the
Stieltjes-measure/Radon--Nikodym theorem for a pointwise summable series of
globally monotone functions. On the interior of $[0,1]$, the clamp is locally
the identity, so the resulting derivative identity transfers back to the
original functions. Tonelli and the fundamental theorem of calculus give the
finite integral of the derivative series. Endpoints and points where some
$f_n$ is not differentiable form a null set, exactly matching the definition
of $g$ in the problem.
