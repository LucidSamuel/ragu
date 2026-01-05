# Revdot Product

Step 5 of our [NARK](../nark.md#nark-1) involves a special case of inner product
argument of the following form:

$$
\Rel_{rdp}=\bigg\{\begin{align*}
\inst&=(\bar{A},\bar{B}\in\G, c\in\F),\\
\wit&=(\v{a},\v{b}\in\F^{4n},\gamma_a,\gamma_b\in\F)\end{align*}:

\begin{align*}
&\phantom{-} \bar{A}=\com(\v{a};\gamma_a) \\
&\land \bar{B}=\com(\v{b};\gamma_b)\\
&\land \revdot{\v{a}}{\v{b}}=c
\end{align*}
\bigg\}
$$

where the prover is trying to convince the verifier that the revdot product
of two secret vectors $\v{a}, \v{b}$ is value $c$ given only their hiding
commitments $\bar{A}, \bar{B}$.
We call them **revdot product relations**.

Revdot products show up in different contexts in Ragu protocol:

- individual circuits'
  [consolidated constraint](../arithmetization.md#consolidated-constraints)
  enforcement against its public inputs 
- [staging polynomials](../../extensions/staging.md)' well-formness check 
  via enforcing its revdot product with its _stage mask_ polynomial
- Folded accumulator $\acc.\v{a}, \acc.\v{b}$ from the previous PCD step

## Intuition

Since revdot product is a special case of inner product relations, and the
concrete commitment scheme we use, Pedersen Vector commitment, is _linearly
homomorphic_, we can borrow the aggregation technique from Bulletproofs:
aggregating multiple claims into one via **random linear combination**.

Specifically, given:

$$
\begin{align*}
\wit &:= &\v{a}_0,\ldots,\v{a}_{n-1}, 
&\phantom{-} \v{b}_0,\ldots,\v{b}_{n-1},
&\phantom{-} \set{\gamma_{a,i}, \gamma_{b,i}}\\

\inst &:= &\bar{A}_0,\ldots,\bar{A}_{n-1}, 
&\phantom{-} \bar{B}_0,\ldots,\bar{B}_{n-1},
&\phantom{-} c_0,\ldots,c_{n-1}
\end{align*}
$$

The verifier can provide two random challenges $\mu,\nu\in\F$, with the goal
of aggregating $n$ revdot claims into one:

$$
\begin{align*}
\wit &:= \v{a}^\ast = \sum_i \mu^{-i}\cdot \v{a}_i,
&\phantom{-} \v{b}^\ast = \sum_i (\mu\nu)^i \cdot \v{b}_i,
&\phantom{-} \sum_i \mu^{-i}\gamma_{a,i}, \sum_i (\mu\nu)^i \gamma_{b,i}\\

\inst &:= \bar{A}^\ast = \sum_i \mu^{-i}\cdot \bar{A}_i,
&\phantom{-} \bar{B}^\ast = \sum_i (\mu\nu)^i\cdot \bar{B}_i,
&\phantom{-} c^\ast = \sum_{i,j} \mu^{j-i} \nu^j e_{i,j}
\end{align*}
$$

where $e_{i,j}=\revdot{\v{a}_i}{\v{b}_j}$ and particularly $e_{i,i} = c_i$.
Notice the verifier can only compute $\bar{A}^\ast, \bar{B}^\ast$ unassisted.
To compute $c^\ast$, he needs _cross terms_ $\set{e_{i,j}}_{i\neq j}$ in addition
to the $\set{c_i}$ terms he already has. For soundness, we require the prover
to send (thus commit to) these cross terms before the verifier samples $\mu,\nu$.

```admonish tip title="Off-diagonal Error Terms"
We can also view the expanded expression of $c^\ast$ as the summation of all
cells in a $n\times n$ matrix where the $(i,j)$-th cell holds the value

$$
\revdot{\mu^{-i}\cdot \v{a}_i}{(\mu\nu)^j \cdot \v{b}_j} = \mu^{j-i} \nu^j \cdot e_{i,j}
$$

for $\forall i,j \in[n]$.
In this matrix view, all the diagonal entries are $\nu^i\cdot c_i$, computable
by the verifier unassisted. Meanwhile, all off-diagonal entries (i.e. $i\neq j$)
contains **error terms** that made up the remaining summands.
We use _cross terms_ and _error terms_ interchangeably.
```

## Revdot Product Reduction

The accumulator instance and witness defined in the split-accumulation scheme
are identical to that of the revdot product relation $\Rel_{rdp}$.
We fold new revdot claims from various sources into $\acc_i$ to derive $\acc_{i+1}$.
This procedure is effectively aggregating all new revdot claims, including the
folded claim in $\acc_i$, into a single claim captured by the updated accumulator.

The split-accumulation proceeds as follows:

1. Prover and verifier parse $\acc_i$ and new revdot claims from proofs
   $\set{\pi_i}$ to be accumulated into the instance-witness pair
   [as above](#intuition).
   The verifier holds $\set{\bar{A}_i,\bar{B}_i, c_i}_{i\in[n]}$.
2. Prover sends all $(n-1)^2$ (off-diagonal) error terms $\set{e_{i,j}}_{i\neq j}$.
3. Verifier samples $\mu,\nu \sample\F$
4. Prover updates the folded witness:
   $$
   \acc_{i+1}.\wit = (
       \underbrace{\sum_i \mu^{-i}\cdot \v{a}_i}_{\v{a}^\ast},\,
       \underbrace{\sum_i (\mu\nu)^i \cdot \v{b}_i}_{\v{b}^\ast},\,
       \underbrace{\sum_i \mu^{-i}\gamma_{a,i}}_{\gamma_a^\ast},\,
       \underbrace{\sum_i (\mu\nu)^i \gamma_{b,i}}_{\gamma_b^\ast}
   )
   $$

   Verifier updates the folded instance:
   $$
   \acc_{i+1}.\inst = (
       \underbrace{\sum_i \mu^{-i}\cdot \bar{A}_i}_{\bar{A}^\ast},\,
       \underbrace{\sum_i (\mu\nu)^i \cdot \bar{B}_i}_{\bar{B}^\ast},\,
       \underbrace{\sum_{i,j} \mu^{j-i} \nu^j e_{i,j}}_{c^\ast}
   )
   $$
   
Notice the majority of verifier's work is $2\cdot \mathsf{MSM}(n)$ to compute
$\bar{A}^\ast, \bar{B}^\ast$; and $O(n^2)$ amount of field multiplications to
compute $c^\ast$. While the $c^\ast$ computation will be constrained in circuit
natively (in $\F_p$), the actual group operations will be 
[deferred](../../prelim/nested_commitment.md#deferred-operations)
to $\F_q$ circuit to avoid expensive non-native arithmetic in the circuit.
In the $\F_p$ circuit, we only witness the nested commitments of
$\bar{A}^\ast, \bar{B}^\ast$ whose coordinates are native in $\F_p$.

## 2 Layer Reduction

Another challenge comes from the $O(n^2)$ field operations for deriving $c^\ast$.
