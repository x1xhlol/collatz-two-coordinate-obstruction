# Positive binary secondary slopes cannot start upper rule removal

Use the normalized upper interpretations from [upper-boundary-normalization.md](upper-boundary-normalization.md):
\[
F_j(x,y)=(x+q_jy+h_j,\ z_jy+k_j),\qquad
C(x,y)=(x+\kappa y,0),\quad D(x,y)=(x,\tau),
\]
with all coefficients nonnegative real numbers. All eleven forward rules are weak coefficientwise, and strictness means a positive first-offset gap.

**Theorem.** If \(z_a>0\) and \(z_b>0\), every first-offset gap is zero. Thus this entire positive-binary-slope branch cannot begin full-system rule removal. No coefficient bound or integrality assumption is used.

The theorem includes the degenerate case \(z_e=z_f=z_g=0\), where \(z_a,z_b\) need not be equal. It does not address a zero binary slope.

The fixed forward rules are

```text
ad -> d       bd -> gd
ae -> ea      af -> eb      ag -> fa
be -> fb      bf -> ga      bg -> gb
ce -> cb      cf -> caa     cg -> cab
```

## 1. Two already reducible cases

If every \(q_j=0\), all digit matrices are diagonal, and [diagonal-digit-obstruction.md](diagonal-digit-obstruction.md) proves that every first-offset gap vanishes.

We also need the following fact, which does not require positive binary slopes.

**Zero-secondary-offset lemma.** If every \(k_j=0\), every first-offset gap vanishes.

Indeed, digit first offsets then compose additively. The six swap first-offset inequalities have sum zero and force
\[
h_a=h_b=R,\qquad h_e=h_f=h_g=U.
\]
The boundary rule `cf -> caa` gives \(U\ge2R\). If \(\tau=0\), the dynamic rule `bd -> gd` gives \(R\ge U\), proving \(R=U=0\) and every first-offset gap zero.

Suppose \(\tau>0\). The two secondary dynamic inequalities give
\[
z_a\ge1,\qquad z_b\ge z_g.
\]
The first dynamic inequality for `bd` gives
\[
(q_b-q_g)\tau\ge U-R\ge0,
\]
so \(q_b\ge q_g\). Consider the scalar maps
\[
\psi_j(y)=z_jy+q_j,\qquad \psi_c(y)=\kappa,
\qquad \psi_d(y)=y.
\]
The swap matrix inequalities become exactly the scalar inequalities for the word-reversed swaps, since \(q_{uv}=q_v+z_vq_u\). The normalized boundary matrix inequalities become the three reversed scalar boundary inequalities. The displayed dynamic inequalities, together with \(q_a\ge0\), give both reversed scalar dynamic rules. Thus all eleven reversed scalar rules are weak. The reversed theorem in [scalar-top-obstruction.md](scalar-top-obstruction.md) gives
\[
q_a=0,\qquad q_b=q_g.
\]
Now `bd` gives \(R\ge U\), so again \(R=U=0\). The first dynamic gaps are \(q_a\tau+R\) and \((q_b-q_g)\tau+R-U\), both zero. The swap and boundary gaps are zero as well. This proves the lemma.

We may therefore assume below that
\[
\sum_j q_j>0,\qquad \sum_j k_j>0. \tag{1}
\]

## 2. Aggregate identities retain all cross terms

Put
\[
\begin{aligned}
p&=z_a+z_b-2,&r&=z_e+z_f+z_g-3,\\
Q&=q_a+q_b,&P&=q_e+q_f+q_g,\\
R&=k_a+k_b,&K&=k_e+k_f+k_g.
\end{aligned}
\]
Summing the six swap gaps separately in the upper-right matrix entry, the secondary offset, and the first offset gives
\[
G_q=rQ-pP\ge0,\qquad
G_k=pK-rR\ge0,\qquad
G_h=QK-PR\ge0.
\tag{2}
\]
The last formula includes every \(q_jk_i\) term; none is discarded. Direct multiplication gives
\[
RG_q+QG_k=pG_h,\qquad
KG_q+PG_k=rG_h.
\tag{3}
\]
If \(p<0\) or \(r<0\), the corresponding identity forces \(G_h=0\). Both identities then have zero right-hand side. Adding them and using (1) gives
\[
G_q=G_k=G_h=0.
\tag{4}
\]
Each is a sum of six nonnegative coordinate gaps, so every individual swap gap in those three coordinates vanishes. The secondary slope gaps always have sum zero as well. Thus in this situation all six digit-swap affine identities are exact.

## 3. The slope partition

The six secondary slope inequalities are exact, by the preceding sum-zero observation. In particular,
\[
z_a(z_g-z_f)=0,\qquad z_b(z_e-z_f)=0.
\]
Since both binary slopes are positive,
\[
z_e=z_f=z_g=s\ge0.
\]
If \(s>0\), the relation \(z_az_f=z_ez_b\) also gives
\[
z_a=z_b=t>0.
\tag{5}
\]
When \(s=0\), this last conclusion does not follow; that branch is treated separately.

## 4. A scalar equality calculation

For use when \(s,t>0\), consider exact swap identities between matrices
\[
A=\begin{pmatrix}\alpha&a\\0&\rho\end{pmatrix},\quad
B=\begin{pmatrix}\alpha&b\\0&\rho\end{pmatrix},
\]
and \(E,F,G\) with diagonals \((\beta,\sigma)\) and upper-right entries \(e,f,g\). All four diagonal parameters are positive.

If \(a=b\), invertibility and the identities \(AE=EA, AF=EB, AG=FA\) give \(E=F=G\). Their remaining commutation relation is
\[
(\alpha-\rho)e=(\beta-\sigma)a.
\tag{6}
\]
If \(d=b-a\ne0\), put \(v=f-e,w=g-e\). Subtracting the baseline commutation relation from the other exact identities gives
\[
\alpha v=\beta d,\quad
(\sigma-\beta)d=\rho v,\quad
\alpha w=\rho v,\quad
(\alpha-\rho)w=(\beta-\sigma)d.
\]
Elimination yields \(\rho(2\alpha-\rho)=0\). Since \(\rho>0\), unequal binary upper-right entries therefore require
\[
\rho=2\alpha,\qquad \sigma=3\beta.
\tag{7}
\]

For the digit matrix \(q\)-entries, this exceptional pair is \((t,s)=(2,3)\). Outside that pair, exact swap matrices force
\[
q_a=q_b=x,\qquad q_e=q_f=q_g=y,
\qquad (1-t)y=(1-s)x.
\tag{8}
\]
For the scalar maps \(y\mapsto z_jy+k_j\), represented by upper-triangular matrices with diagonals \((z_j,1)\), the exceptional pair is instead \((t,s)=(1/2,1/3)\). Outside that pair, exact swap secondary maps force
\[
k_a=k_b=v,\qquad k_e=k_f=k_g=w,
\qquad (1-s)v=(1-t)w.
\tag{9}
\]

## 5. Positive ternary slopes with at least one slope below one

Suppose \(s,t>0\) and \(\min(s,t)<1\). Then \(p=2(t-1)<0\) or \(r=3(s-1)<0\), so all six swap identities are exact by section 2.

The \(q\)-exceptional pair \((2,3)\) is outside this region. Equation (8), nonnegativity, and the nonzero total \(q\) in (1) therefore imply
\[
0<s,t\le1,\qquad
q_j=\lambda(1-z_j)\quad\text{for every digit},
\qquad\lambda>0.
\tag{10}
\]
For example, if \(t<1\), (8) rules out \(s>1\), and \(\lambda=x/(1-t)>0\); the case \(t=1,s<1\) follows using \(y/(1-s)\).

The positive row \((1,\lambda)\) is fixed by every digit matrix. Set
\[
H_j=h_j+\lambda k_j\ge0.
\]
Projected digit offsets therefore compose additively. The exact swap identities imply
\[
H_a=H_b=L,\qquad H_e=H_f=H_g=N.
\tag{11}
\]
Projecting the weak dynamic rule `bd -> gd` by this positive row gives
\[
L\ge N.
\tag{12}
\]

Outside the \(k\)-exceptional pair \((1/2,1/3)\), (9) and the nonzero total \(k\) give a number \(\mu>0\) such that
\[
k_j=\mu(1-z_j)
\tag{13}
\]
for every digit. For any digit word \(w\), these relations give
\[
q_w=\lambda(1-z_w),\quad k_w=\mu(1-z_w),
\quad h_w=H_w-\lambda k_w,
\]
where \(H_w\) is the sum of its digit \(H\)-values.

For a boundary comparison \(c\ell\to cr\), write its matrix and first-offset gaps as \(B_q,B_h\). Then
\[
B_q=(\kappa-\lambda)(z_\ell-z_r)\ge0,
\qquad
B_h=H_\ell-H_r-\mu B_q\ge0.
\]
In particular, `cf -> caa` gives \(N\ge2L\). Together with (12), this forces \(L=N=0\). Since \(H_j=h_j+\lambda k_j\), nonnegativity and \(\lambda>0\) force every \(k_j=0\), contradicting (1).

At the exceptional pair \((t,s)=(1/2,1/3)\), equation (10) still holds. The matrix gaps of `ce` and `cf` are
\[
(\kappa-\lambda)(s-t),\qquad
(\kappa-\lambda)(s-t^2).
\]
The two factors \(s-t=-1/6\) and \(s-t^2=1/12\) have opposite signs. Thus both gaps can be nonnegative only if \(\kappa=\lambda\). The first-offset boundary comparisons then compare exactly the \(H\)-sums, so `cf` again gives \(N\ge2L\). The same contradiction follows.

Consequently (1) is impossible throughout this region. Section 1 disposes of the remaining zero-total cases, proving the theorem here.

## 6. Positive ternary slopes with both slopes at least one

Suppose \(t,s\ge1\). The pair \(t=s=1\) is already excluded by [upper-unit-diagonal-obstruction.md](upper-unit-diagonal-obstruction.md).

First assume \(s\le t\), so \(t>1\). Put \(\alpha=q_a,\beta=q_b\), and \(P=q_e+q_f+q_g,Q=q_a+q_b\). The three boundary matrix inequalities imply
\[
q_e\ge\beta,\qquad
q_f\ge(1+t)\alpha,\qquad
q_g\ge\beta+t\alpha,
\]
because their omitted \(\kappa\)-terms are respectively \(\kappa(t-s)\) and \(\kappa(t^2-s)\), all nonnegative. Hence
\[
P\ge2\beta+(1+2t)\alpha\ge2Q.
\]
But the aggregate upper-right inequality is
\[
3(s-1)Q-2(t-1)P\ge0,
\]
so
\[
P\le\frac{3(s-1)}{2(t-1)}Q\le\frac32Q.
\]
Therefore \(P=Q=0\). Every \(q_j\) vanishes, and the diagonal-digit result applies.

Now assume \(s>t\ge1\). The secondary-offset inequality for `bg` gives
\[
(t-1)k_g\ge(s-1)k_b.
\]
The secondary dynamic inequality gives
\[
k_b\ge k_g+(s-t)\tau\ge k_g.
\]
Combining them forces \(k_b=0\), since otherwise \((s-1)k_b>(t-1)k_b\ge(t-1)k_g\). Consequently \(k_g=\tau=0\). This argument includes \(t=1\).

The secondary inequalities for `ag` and `af` now give
\[
-(s-1)k_a-k_f\ge0,
\qquad -k_e\ge0,
\]
so every \(k_j=0\). The zero-secondary-offset lemma finishes this case.

## 7. All three ternary slopes zero

Finally suppose
\[
z_a=a>0,\qquad z_b=b>0,\qquad z_e=z_f=z_g=0.
\]
The two binary slopes are allowed to differ. Here \(r=-3<0\), so under (1) section 2 makes every swap affine identity exact.

Write \(e=q_e,f=q_f,g=q_g\). The exact upper-right relations `af`, `be`, `ag`, and `bf` give
\[
f=q_b+be,\quad e=q_b+bf,\quad
g=q_a+af,\quad f=q_a+ag.
\]
Thus \((1+b)(f-e)=0\) and \((1+a)(g-f)=0\). All three ternary upper-right entries are equal to a number \(\lambda\). The commuting identities `ae`, `bg` then give
\[
q_a=\lambda(1-a),\qquad q_b=\lambda(1-b).
\]
By (1), \(\lambda>0\), so \(a,b\le1\). In other words, (10) again holds for all five digits.

The exact secondary-offset relations are equally explicit. From `ae` and `af`,
\[
k_a=(1-a)k_e,\qquad k_a+ak_f=k_e.
\]
Since \(a>0\), this forces \(k_f=k_e\); `ag` then forces \(k_g=k_e\). Finally `bg` gives \(k_b=(1-b)k_g\). Thus (13) holds with \(\mu=k_e>0\).

The common positive row, the projected values \(L,N\), and the two boundary-gap identities from section 5 now apply without change. They imply \(L\ge N\ge2L\), hence all \(k_j=0\), contradicting (1). The zero-total cases are already covered by section 1.

This proves the theorem for every positive pair \(z_a,z_b\), including zero ternary slopes and all boundary values. The remaining branches have at least one zero binary secondary slope. No result about those branches is asserted here.
