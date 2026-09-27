# A necessary condition for an upper-triangular swap decrease

Consider the five nonnegative real affine digit maps

\[
F_s(x,y)=(x+q_sy+h_s,\ z_sy+k_s),
\qquad s\in\{a,b,e,f,g\}.
\]

Assume the six swaps are weak coefficientwise, with leftmost-outermost
composition:

```text
ae -> ea      af -> eb      ag -> fa
be -> fb      bf -> ga      bg -> gb
```

No boundary rule, coefficient bound, or positivity of the secondary slopes
is assumed. Define the group totals

\[
\begin{array}{lll}
Q=q_a+q_b,&P=q_e+q_f+q_g,\\
R=k_a+k_b,&K=k_e+k_f+k_g,\\
p=z_a+z_b-2,&r=z_e+z_f+z_g-3.
\end{array}
\]

Let \(G_q,G_k,G_h\) be the sums of the six gaps in the upper-right
matrix entry, second offset, and first offset, respectively. Every one
of the individual gaps, and hence each sum, is nonnegative.

For two digits, composition gives

\[
q_{uv}=q_v+q_uz_v,\qquad
k_{uv}=k_u+z_uk_v,\qquad
h_{uv}=h_u+h_v+q_uk_v.
\]

The left sides of the six rules contain all six binary-then-ternary
pairs, and their right sides contain all six ternary-then-binary pairs.
Summing therefore gives the exact identities

\[
G_q=rQ-pP,\qquad
G_k=pK-rR,\qquad
G_h=QK-PR.
\tag{1}
\]

Consequently

\[
R G_q+Q G_k=pG_h,\qquad
K G_q+P G_k=rG_h.
\tag{2}
\]

The left sides of (2) are nonnegative. If \(p<0\) or \(r<0\),
nonnegativity of \(G_h\) forces \(G_h=0\). Since it is a sum of
six nonnegative first-offset gaps, each of those gaps is zero.

Thus a strict first-offset decrease in any swap requires both

\[
z_a+z_b\ge2,\qquad z_e+z_f+z_g\ge3.
\]

These are necessary conditions, not sufficient ones. The argument does
not decide the dynamic or boundary gaps, does not exclude all
upper-triangular certificates, and does not prove Collatz convergence.
