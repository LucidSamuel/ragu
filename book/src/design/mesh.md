# Mesh Polynomial

Given a collection of $N$ circuits, each represented by a bivariate polynomial $s_i(X, Y)$, the mesh is a higher-level trivariate polynomial $m(W, X, Y)$ that interpolates these circuits, such that   

$$
m(\omega^i, X, Y) = s_i(X, Y)
$$

for some root of unity $\omega \in \mathbb{F}$ of sufficiently large $2^k$ order to index all circuits. Evaluating the mesh at any domain point $W = \omega^i$ recovers exactly the $i$-th circuit's bivariate polynomial.

## Construction 

The mesh is a collection of circuits over a particular field, and the mesh has a *domain*, where each circuit is mapped to a successive power of $\omega$ in the domain. 

Our protocol enforces consistency checks by evaluating the mesh polynomial at Fiat-Shamir challenge points. We restrict the dimensions and partially evaluate $m$ at specific $W$ or $X$ or $Y$ values to obtain polynomials in the remaining variables.

| Evaluation | Type | Description |
|------------|------|-------------|
| $m(W, x, y)$ | $\mathbb{F}[W]$ | Polynomial in $W$ for fixed $x$ and $y$ |
| $m(w, X, y)$ | $\mathbb{F}[X]$ | Polynomial in $X$ for fixed $w$ and $y$ |
| $m(w, x, Y)$ | $\mathbb{F}[Y]$ | Polynomial in $Y$ for fixed $w$ and $x$ |
| $m(w, x, y)$ | $\mathbb{F}$ | Point evaluation at specific coordinates |

For instance, the mesh $m(W, x, y)$ is the polynomial indeterminately in $W$ that interpolates all circuit points. At each point $\omega$ in the domain, the mesh polynomial equals the $i$-th circuit's evaluation: 

$$
m(\omega^i, x, y) = s_i(x, y)
$$

These consistency checks may require evaluating the mesh polynomial indeterminately in $X$:

$$
m(\omega^i, X, y) \;\equiv\; s_i(X, y)
$$

More generally, the protocol needs to evaluate the mesh at *arbitrary* Fiat-Shamir challenge points $w \in \mathbb{F}$ (not necessarily a root of unity $\omega$). We use Lagrange coefficients for polynomial interpolation. Suppose the mesh is defined on the points ${\omega^0, \omega^1, ..., \omega^{n-1}}$ with 

$$
f_i(X,y) \;=\; m(\omega^i, X, y) \;=\; s_i(X,y)
$$

Then for any $w \in \mathbb{F}$

$$
m(w, X, y) \;=\; \sum_{i=0}^{n-1} \ell_i(w)\, f_i(X,y)
$$

where the Lagrange basis coefficients are

$$
\ell_i(w) \;=\; \prod_{\substack{0\le j< n\\ j\ne i}} \frac{w-\omega^j}{\omega^i-\omega^j}.
$$

This gives you a polynomial that *(i)* passes through all circuit evaluations at their respective $\omega^i$ points, and *(ii)* evaluates to the correct interpolated value at the random challenge point $W = w$.

## Consistency Checks

We sample random $w_i$ to evaluate different mesh polynomial slices $m(w_i, x_i, y_i)$ held by different accumulators being folded. The objective is to verify these slices come from the same underlying mesh $m(W, X, Y)$.

$$
s_1(W) := m(W, x_1, y_1​)
$$

$$
s_2(W) := m(W, x_2​, y_2​)
$$

and each accumulator holds a univariate-in-$W$ slice of the mesh:

$$
acc_1​.s(w_1​) = m(w_1,x_1​,y_1​)
$$

$$
acc_2​.s(w_2​) = m(w_2,x_2,y_2​)
$$

The prover will compute $m(w, x_i, Y)$ polynomial indeterminately in $Y$ for each of the accumulators. Only *after* committing to the circuit witnesses and relevant polynomials does the verifier derive fresh Fiat-Shamir challenges $y$ and $w$ to check mesh consistency. The checks verify 

$$
m\big(w, x_1, Y\big)\Big|_{Y=acc_1.y}
\;=\;
s_1(W)\Big|_{W=w}
\;=\;
m\big(w, x_1, y_1\big)
$$

and equivalently,

$$
m\big(w,\ X,\ \texttt{acc}_1.y\big)\Big|_{X=\texttt{acc}_1.x}
\;=\;
m\big(w,\ \texttt{acc}_1.x,\ Y\big)\Big|_{Y=\texttt{acc}_1.y}
\;=\;
m\big(w,\ \texttt{acc}_1.x,\ \texttt{acc}_1.y\big)
$$

By using random $w$, the verifier ensures all partial views are consistent with the same underlying mesh polynomial.

## Flexible Mesh Sizes via Domain Extension

The mesh requires a domain size $2^k$ for some non-negative integer k and assigns circuits to successive powers $\omega^j$, where $\omega$ is a $2^k$ primitive root of unity in the field. The domain size determines the degree of the interpolation polynomial. 

A naive approach to mesh construction would assign the $j$-th circuit directly to $\omega^j$ where $\omega$ is chosen based on the domain size $2^k$ needed to fit all circuits. However, this creates a fundamental problem: **the domain size must be known in advance**. If we allocate a $2^k$ domain and later register a $(2^k+1)$-th circuit into the mesh, we would outgrow the mesh. 

This limitation is cleverly resolved through *rolling domain extensions*: the domain is "rolling" in the sense that the mesh accepts circuits incrementally without knowing the final domain size $k$. When $k$ is fixed at finalization, bit-reversal maps each circuit to its correct position in the finalized domain.


### Bit-Reversal

The way this construction works is $\omega$ values are *precomputed* in the maximal field domain $2^S$; the actual working domain $2^k$ is determined later and depends on the number of circuits that end up being registered in the mesh. The precomputation remains valid regardless of $k$.

To assign a domain point to the $j$-th circuit, we don't use $\omega^j$ directly. Instead, we fix a maximal upper bound $k = S$ and set

$$
i := \text{bitreverse}(j, S)
$$

where we reverse the bits of $j$ to compute the power $i$, and assign circuit $j$ to domain point $\omega^i$. This bit-reversal ensures  we effectively exhaust the smaller domains first. 

During mesh finalization when $k$ is determined, the circuit's position in the mesh is computed by right-shifting 

$$
\text{position} = \text{bitreverse}(j, S) \gg (S - k)
$$

This effectively compresses the $2^S$-slot domain to the $2^k$-slot domain, where $k = \lceil \log_2 N \rceil$. 
 
Consequently, circuit synthesis can compute $\omega^i$ at compile-time, independent of the mesh construction itself. This has the property that the domain element assigned to circuit $j$ depends only on the circuit index $j$ and the fixed maximal bound $S$, not on the total number of
circuits $N$.
