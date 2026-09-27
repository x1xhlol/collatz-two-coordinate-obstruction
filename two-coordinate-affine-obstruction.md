# No full two-coordinate affine rule-removal certificate

Consider the complete mixed-base rewriting system

```text
ad -> d       bd -> gd
ae -> ea      af -> eb      ag -> fa
be -> fb      bf -> ga      bg -> gb
ce -> cb      cf -> caa     cg -> cab
```

Words compose with their leftmost symbol outermost. For each of the seven
symbols, let

\[
F_s(x)=M_sx+v_s,\qquad
M_s\in\mathbb R_{\ge0}^{2\times2},\quad
v_s\in\mathbb R_{\ge0}^{2},\quad (M_s)_{00}\ge1.
\]

A rule \(\ell\to r\) is weak if
\(M_\ell\ge M_r\) and \(v_\ell\ge v_r\) entrywise. The strict
criterion requires, in addition, a positive first-offset gap
\((v_\ell)_0-(v_r)_0>0\). This is the full-context criterion treated in
[the real unit-gap proof](real-affine-unit-gap.md); a common rescaling of
all offsets turns any selected positive gap into a unit gap.

**Theorem.** If all eleven rules are weak, every first-offset gap is zero.
The same statement holds when every word on both sides of every rule is
reversed, preserving each rule's direction.

Consequently no interpretation in this class can remove even a first
rule from the complete system. This covers arbitrary nonnegative real
coefficients, including zero entries and singular matrices, with no
coefficient or intermediate-result bound. It is stronger than the finite
search exclusions, and does not use their solver outcomes.

## Proof for forward words

The [aggregate matrix theorem](aggregate-matrix-obstruction.md) forces
all five digit matrices \(M_a,M_b,M_e,M_f,M_g\) to share an upper or
lower triangular orientation in the original coordinates. The
[first-diagonal theorem](triangular-first-diagonal.md) forces each of
their first diagonal entries to be exactly one. Neither theorem
restricts the boundary matrices to triangular form.

If the digit matrices are lower triangular,
[the lower affine theorem](lower-triangular-affine-obstruction.md)
already forces every first-offset gap to vanish, with arbitrary
admissible boundary matrices and offsets.

If they are upper triangular,
[exact boundary normalization](upper-boundary-normalization.md)
preserves all weak rules and all first-offset gap signs while reducing to

\[
F_s(x,y)=(x+q_sy+h_s,\ z_sy+k_s),\qquad
C(x,y)=(x+\kappa y,0),\quad D(x,y)=(x,\tau).
\]

The two remaining cases are exhaustive:

| Secondary binary slopes | Result |
|---|---|
| \(z_a>0\) and \(z_b>0\) | [Positive-slope theorem](upper-positive-slopes.md): every first-offset gap is zero. |
| \(z_a z_b=0\) | [Zero-slope theorem](upper-zero-slopes.md): every first-offset gap is zero. |

The positive-slope proof includes all-zero ternary slopes with unequal
positive binary slopes, both scalar equality resonances, and slopes equal
to one. The zero-slope proof includes both binary slopes zero, zero sums
of the upper-right entries or secondary offsets, and its exceptional
ternary slope pattern. All affine cross terms are retained.

Thus every normalized upper gap is zero. Normalization preserved whether
each gap was positive, and the original gaps were nonnegative. Therefore
every original upper gap is zero as well. This proves the forward claim.

## Proof for reversed words

The necessary aggregate and first-diagonal matrix reductions apply to
reversed words by transposing each symbol's matrix. This step concerns
the matrix parts only; it makes no assertion about affine transposition.

[The reversed affine proof](reversed-triangular-affine-obstruction.md)
then treats both possible triangular orientations. It directly excludes
every reversed lower-triangular model, including arbitrary boundary
offsets. For a reversed upper model, an exact boundary normalization
followed by the homogeneous product-reversing map
\(H\mapsto JH^{\mathsf T}J\) produces an admissible forward upper
model, preserving first-offset gap signs. The forward claim just proved
excludes a positive gap there. Hence every reversed gap is zero too.

## What the theorem does and does not establish

The theorem excludes full two-coordinate affine certificates with the
stated nonnegativity, monotonicity, weak-comparison, and strict-gap
conditions. A sequence of rule-removal steps entirely within this class
cannot begin on the complete eleven-rule system.

It does not exclude certificates in higher dimensions, top-rewriting
interpretations that allow smaller first diagonal entries, nonlinear
interpretations, different orders, or a proof that first applies a
different sound transformation. It also makes no claim that a subsystem
obtained by deleting a rule has no certificate.

This is a limitation of a proof method. It neither proves universal
Collatz convergence nor constructs a cycle or divergent positive orbit.
The Collatz conjecture remains unresolved by this work.
