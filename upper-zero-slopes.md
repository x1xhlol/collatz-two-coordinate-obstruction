# Upper triangular interpretations with a zero binary secondary slope

This note excludes a first full-system rule-removal step whenever at least one of the two binary digit secondary slopes is zero. All coefficients are arbitrary nonnegative real numbers. The proof retains every affine cross term.

## Setting and statement

Use the exact boundary normalization from [upper-boundary-normalization.md](upper-boundary-normalization.md):

\[
F_s(x,y)=(x+q_sy+h_s,\ z_sy+k_s),
\qquad C(x,y)=(x+\kappa y,0),\qquad D(x,y)=(x,\tau),
\]

with every parameter nonnegative and \(s\in\{a,b,e,f,g\}\). Assume all eleven rules are weak coefficientwise:

```text
ad -> d       bd -> gd
ae -> ea      af -> eb      ag -> fa
be -> fb      bf -> ga      bg -> gb
ce -> cb      cf -> caa     cg -> cab
```

Word composition is leftmost outermost. A strict rule would require a positive first-coordinate offset gap.

**Theorem.** If \(z_a z_b=0\), every rule has zero first-offset gap. Thus this entire zero-binary-slope region admits no first full-system rule removal. By the normalization theorem, this also applies to the corresponding original interpretations with arbitrary admissible boundary maps.

Write \(a,b,e,f,g\) temporarily for the five secondary slopes \(z_s\). The other parameters retain their subscripts.

## 1. Complete partition of the slopes

The six swap slope gaps are nonnegative and sum to zero, so every slope comparison is an equality. The nontrivial equalities are

\[
af=eb,\qquad a(g-f)=0,\qquad b(e-f)=0,\qquad bf=ga.
\tag{1}
\]

Under \(ab=0\), these give exactly three branches:

1. \(a=0,b>0\): \(e=f=0\), while \(g\ge0\) is free.
2. \(b=0,a>0\): \(f=g=0\), while \(e\ge0\) is free.
3. \(a=b=0\): all three ternary slopes are initially free.

If the positive binary slope exceeds one, all five upper right coefficients vanish. For branch 1 with \(b>1\), the `af` and `be` upper right inequalities are

\[
q_f\ge q_b+bq_e,\qquad q_e\ge q_b+bq_f.
\]

Their sum forces \(q_e=q_f=q_b=0\). The `ae` inequality then gives \(q_a=0\), and `bg` gives \((1-b)q_g\ge0\), hence \(q_g=0\).

For branch 2 with \(a>1\), the `ag` and `bf` inequalities are

\[
q_g\ge q_a+aq_f,\qquad q_f\ge q_a+aq_g.
\]

Their sum forces \(q_a=q_f=q_g=0\). Then `af` gives \(q_b=0\), and `ae` gives \(q_e=0\).

In either case all digit matrices are diagonal, so [diagonal-digit-obstruction.md](diagonal-digit-obstruction.md) excludes every strict gap. For the rest of this proof, both binary slopes lie in \([0,1]\), and at least one is zero. In particular,

\[
p=a+b-2<0.
\tag{2}
\]

## 2. The aggregate identities eliminate all swap gaps

Use the notation and identities of [upper-aggregate-gap.md](upper-aggregate-gap.md):

\[
Q=q_a+q_b,\quad P=q_e+q_f+q_g,\quad
R=k_a+k_b,\quad K=k_e+k_f+k_g.
\]

Let \(G_q,G_k,G_h\) be the sums of the six swap upper right, secondary-offset, and first-offset gaps. Each individual gap is nonnegative. The identities needed here are

\[
G_h=QK-PR,\qquad R G_q+Q G_k=pG_h.
\tag{3}
\]

Because \(p<0\), (3) forces \(G_h=0\). Hence every swap first-offset gap is zero.

If \(R>0\) but \(Q=0\), the first identity in (3) gives \(P=0\). Thus all five \(q_s\) vanish and the diagonal theorem again applies.

If \(Q>0\) and \(R>0\), the second identity in (3) forces \(G_q=G_k=0\). Every individual swap upper right and secondary-offset gap is therefore zero too. Together with (1), all six affine swap comparisons are exact equalities in this case.

We handle \(R=0\) separately, then use these exact equalities when \(Q,R>0\).

## 3. Vanishing binary secondary offsets

Suppose \(R=0\), so \(k_a=k_b=0\). The secondary swap inequalities imply \(k_e=k_f=k_g=0\). Explicitly, if \(a=0\), `ag` forces \(k_f=0\), `af` forces \(k_e=0\), and `bf` forces \(k_g=0\). If instead \(b=0\), use `be`, `bf`, and `af` in that order.

All affine cross terms \(q_s k_t\) now vanish. The exact first-offset swap equalities give

\[
h_a=h_b=H,\qquad h_e=h_f=h_g=J.
\]

The `cf` first-offset inequality gives \(J\ge2H\).

If \(a<1\), the secondary `ad` inequality is \((a-1)\tau\ge0\), so \(\tau=0\). The first-offset `bd` inequality then gives \(H\ge J\). Hence \(H=J=0\), and all eleven first-offset gaps vanish.

The only remaining possibility is \(a=1,b=0\). Its `ag` and `bf` upper right inequalities force

\[
q_a=0,\qquad q_f=q_g.
\]

The `af` upper right inequality gives \(q_g\ge q_b\). Consequently the first-offset `bd` inequality gives

\[
H-J\ge(q_g-q_b)\tau\ge0.
\]

Again \(H=J=0\), and this inequality forces \((q_g-q_b)\tau=0\). Since \(q_a=0\), the `ad` first gap is also zero. All swap and boundary first gaps vanish. This completes the case \(R=0\).

## 4. A common-fixed-point obstruction

The following observation will close most of the remaining cases. Suppose the exact swap equalities yield, for some \(q,k>0\),

\[
q_s=q(1-z_s),\qquad k_s=k(1-z_s)
\quad\text{for every digit }s.
\tag{4}
\]

Every secondary digit map fixes \(y=k\). Define the first increment on this line by

\[
H_s=h_s+q_sk.
\]

Composition adds these increments. The six exact swap equalities therefore give

\[
H_a=H_b=H,\qquad H_e=H_f=H_g=J.
\tag{5}
\]

For any digit word \(w\), (4) gives

\[
q_w=q(1-z_w),\quad k_w=k(1-z_w),\quad
h_w=H_w-qk(1-z_w),
\]

where \(H_w\) is the sum of the increments of its letters. For a boundary rule \(c\ell\to cr\), its matrix gap is

\[
L=(\kappa-q)(z_\ell-z_r)\ge0,
\]

and its first-offset gap is

\[
H_\ell-H_r-kL\ge0.
\]

Thus \(H_\ell\ge H_r\); in particular `cf` gives \(J\ge2H\).

The secondary gap of `bd` is

\[
S=(b-g)\tau+k_b-k_g=(g-b)(k-\tau)\ge0.
\]

Its first-offset gap is exactly

\[
H-J-qS\ge0.
\]

Consequently \(H\ge J\), and (5) forces \(H=J=0\). But one binary digit has slope zero. For that digit, (4) gives \(H_s=h_s+qk\ge qk>0\), a contradiction.

Therefore the form (4), with \(q,k>0\), is impossible under all eleven weak rules.

## 5. Exactly one binary slope is zero

Assume \(Q,R>0\), so all six swap comparisons are exact by section 2.

In branch 1, \(a=0\), \(0<b\le1\), and \(e=f=0\). Exact upper right comparisons give

\[
q_e=q_a,\quad q_f=q_b+bq_a,\quad q_a=q_b+bq_f,
\quad q_g=(1-g)q_a.
\]

The middle two equalities yield \(q_b=(1-b)q_a\), \(q_f=q_a\). Thus all five upper right coefficients have the form \(q_s=q(1-z_s)\), with \(q=q_a>0\).

Exact secondary-offset comparisons give

\[
k_e=k_f=k_a,\qquad k_b=(1-b)k_a,\qquad k_g=(1-g)k_a.
\]

Thus \(k_s=k(1-z_s)\), with \(k=k_a>0\). Section 4 excludes this case.

In branch 2, \(b=0\), \(0<a\le1\), and \(f=g=0\). Exact upper right comparisons give

\[
q_f=q_b,\quad q_g=q_a+aq_f,\quad q_f=q_a+aq_g,
\quad q_e=(1-e)q_b.
\]

These imply \(q_a=(1-a)q_b\), \(q_g=q_b\). Hence again \(q_s=q(1-z_s)\), now with \(q=q_b>0\).

Exact secondary-offset comparisons give

\[
k_f=k_g=k_b,\qquad k_a=(1-a)k_b,\qquad k_e=(1-e)k_b.
\]

Thus \(k_s=k(1-z_s)\), with \(k=k_b>0\), and section 4 again applies. This includes the endpoint where the positive binary slope is exactly one.

## 6. Both binary slopes are zero

Continue to assume \(Q,R>0\) and exact swaps. Now \(a=b=0\). The exact `af` and `bf` upper right comparisons give

\[
q_f=q_b-fq_a=q_a-fq_b.
\]

Since \(1+f>0\), \(q_a=q_b=q>0\). The remaining comparisons give

\[
q_e=(1-e)q,\qquad q_f=(1-f)q,\qquad q_g=(1-g)q.
\tag{6}
\]

For the secondary offsets, the exact comparisons give

\[
e(k_a-k_b)=0,\qquad
(1-f)(k_a-k_b)=0,\qquad
g(k_a-k_b)=0.
\tag{7}
\]

If \(k_a=k_b=k>0\), those same comparisons give
\(k_s=k(1-z_s)\) for every digit. This is excluded by section 4.

If \(k_a\ne k_b\), (7) forces the exceptional slope pattern

\[
e=g=0,\qquad f=1.
\]

Equations (6) and the exact secondary comparisons then give

\[
q_a=q_b=q_e=q_g=q>0,\quad q_f=0,
\qquad k_e=k_a,\quad k_f=0,\quad k_g=k_b.
\tag{8}
\]

The `cf` matrix inequality gives \(\kappa\ge q\). The exact first-offset swap comparisons give

\[
h_e=h_f-qk_a,\qquad h_g=h_f-qk_b,
\qquad h_a+qk_a=h_b+qk_b.
\tag{9}
\]

Using (8) and (9), the first-offset `bd` inequality implies

\[
h_f\le h_b+qk_b=h_a+qk_a.
\]

The first-offset `cf` inequality instead implies

\[
h_f\ge2h_a+(q+\kappa)k_a.
\]

Combining them gives \(h_a+\kappa k_a\le0\). Nonnegativity and \(\kappa\ge q>0\) force \(h_a=k_a=0\). The last equality in (9) then forces \(h_b=k_b=0\), contradicting \(R>0\). Thus the exceptional pattern is impossible too.

All branches and all zero/nonzero cases for \(Q,R\) are exhausted. Every admissible case has zero first-offset gap in every rule, proving the theorem.

## Scope

This proof excludes the entire normalized upper case with \(z_a z_b=0\), without coefficient bounds, integrality restrictions, or solver output. It does not by itself address the positive-binary-slope region. Its only prior obstruction dependency is the separately proved diagonal-digit case; the aggregate identities and boundary normalization are exact algebraic reductions.
