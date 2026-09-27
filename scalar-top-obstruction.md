# Scalar affine interpretations cannot start either boundary-top proof

This note completely excludes one-dimensional affine certificates for both audited top-rewriting targets: the three forward B-rules and the two reversed D-rules. Coefficients may be arbitrary nonnegative **real** numbers, and slopes may be zero. The result therefore covers the scalar searches whose solver runs timed out.

This is an obstruction to a certificate class, not a proof or disproof of Collatz. It does not cover higher-dimensional, nonlinear, arctic, or differently restricted interpretations.

## Conventions and statement

Interpret the seven ASCII symbols by

\[
\begin{array}{lll}
[a](x)=ax+\alpha,&[b](x)=bx+\beta,&[c](x)=cx+\kappa,\\
[d](x)=dx+\delta,&[e](x)=ex+\varepsilon,&[f](x)=fx+\varphi,\\
[g](x)=gx+\gamma.
\end{array}
\]

All fourteen parameters are nonnegative reals. A lowercase letter on the right denotes its symbol's slope. Word composition is leftmost outermost, so `[uv]=[u]∘[v]`. A weak rule requires both its slope and constant coefficient to be nonincreasing. A strict top rule in the audited framework additionally requires a positive uniform constant gap; the checker uses a gap of at least one.

The fixed system is

```text
ad -> d       bd -> gd
ae -> ea      af -> eb      ag -> fa
be -> fb      bf -> ga      bg -> gb
ce -> cb      cf -> caa     cg -> cab
```

**Theorem.**

1. If all eleven forward rules are weak, the constant gaps of `ce -> cb`, `cf -> caa`, and `cg -> cab` are all zero.
2. If all eleven reversed rules are weak, the constant gaps of `da -> d` and `db -> dg` are both zero.

Consequently neither scalar top target admits even a first relative rule-removal step. No positive lower bound on symbol slopes is assumed.

## Forward B-rules

The three constant gaps are

\[
c(\varepsilon-\beta),\qquad
c\bigl(\varphi-(a+1)\alpha\bigr),\qquad
c(\gamma-a\beta-\alpha).
\tag{1}
\]

If \(c=0\), they vanish. Suppose \(c>0\). Dividing the weak B-inequalities by \(c\) yields

\[
e\ge b,\quad f\ge a^2,\quad g\ge ab,
\qquad
\varepsilon\ge\beta,\quad
\varphi\ge(a+1)\alpha,\quad
\gamma\ge a\beta+\alpha.
\tag{2}
\]

The sum of the six swap slope differences is zero, since both sums equal \((a+b)(e+f+g)\). Every difference is nonnegative, so each is zero. The nontrivial equalities are

\[
af=eb,\qquad a(g-f)=0,\qquad b(e-f)=0,\qquad bf=ga.
\tag{3}
\]

If \(a=0\), then \(eb=0\) and \(e\ge b\), forcing \(b=0\). Conversely, if \(b=0\), then \(af=0\) and \(f\ge a^2\), forcing \(a=0\). If both are positive, (3) and (2) instead imply

\[
a=b=t>0,\qquad e=f=g=s\ge\max(t,t^2).
\tag{4}
\]

These two cases exhaust all nonnegative slopes.

### Positive binary slopes

The constant inequality for `bd -> gd` is

\[
\beta-\gamma\ge(s-t)\delta\ge0.
\]

Together with (2), this gives

\[
\beta\ge\gamma\ge t\beta+\alpha,
\qquad \alpha\le(1-t)\beta.
\tag{5}
\]

If \(t>1\), (5) forces \(\alpha=\beta=\gamma=0\). The constant inequalities for `ag -> fa` and `af -> eb` then force \(\varphi=\varepsilon=0\).

If \(t=1\), (5) gives \(\alpha=0\), \(\gamma=\beta\). The same two swap rules give

\[
\varphi\le\beta,
\qquad
\varphi\ge s\beta+\varepsilon\ge2\beta,
\]

where the last inequality uses \(s\ge1\) and \(\varepsilon\ge\beta\). Thus again every digit constant is zero.

If \(0<t<1\), the constant inequality for `ae -> ea` gives

\[
(1-t)\varepsilon\le(1-s)\alpha\le(1-t)\alpha,
\]

because \(s\ge t\). Hence

\[
\beta\le\varepsilon\le\alpha\le(1-t)\beta.
\]

Since \(t>0\), this forces \(\beta=0\), followed by \(\alpha=\varepsilon=\gamma=0\); `ag -> fa` then forces \(\varphi=0\). In every positive-slope case all three gaps in (1) vanish.

### Both binary slopes zero

Now \(a=b=0\). The inequalities from `ag -> fa` and (2) give

\[
\alpha\ge f\alpha+\varphi\ge\varphi\ge\alpha,
\]

so \(\varphi=\alpha\). From `be -> fb`,

\[
\beta\ge f\beta+\varphi\ge\alpha.
\]

From `ae -> ea` and (2),

\[
\alpha\ge e\alpha+\varepsilon\ge\varepsilon\ge\beta.
\]

Consequently \(\alpha=\beta=\varepsilon=\varphi\). Finally `bf -> ga` and (2) give

\[
\beta\ge g\alpha+\gamma\ge\gamma\ge\alpha,
\]

so \(\gamma=\alpha\) too. Substituting into (1), with \(a=0\), shows that every B-gap is zero. This proves the forward claim.

## Reversed D-rules

The two constant gaps are

\[
[da]-[d]:\quad d\alpha,
\qquad
[db]-[dg]:\quad d(\beta-\gamma).
\tag{6}
\]

If \(d=0\), both vanish. Suppose \(d>0\). The weak slope and constant inequalities for the two reversed dynamic rules imply

\[
a\ge1,\qquad b\ge g,\qquad\beta\ge\gamma.
\tag{7}
\]

The reversed `cg -> cab` rule is `gc -> bac`. Its constant inequality is

\[
\gamma\ge\beta+b\alpha+(ab-g)\kappa.
\tag{8}
\]

Here \(ab-g\ge b-g\ge0\) by (7). Combining (7) and (8) therefore gives

\[
\beta=\gamma,\qquad b\alpha=0.
\tag{9}
\]

The second gap in (6) is already zero. Suppose the first could be positive, so \(\alpha>0\). Equation (9) forces \(b=0\); then (7) forces \(g=0\). The weak slope inequality for reversed `ag -> fa` gives \(ag\ge fa\), so \(f=0\), since \(a\ge1\).

The constant inequalities of the reversed rules `ga -> af` and `fb -> ag` now reduce to

\[
\gamma\ge a\varphi+\alpha,
\qquad
\varphi\ge a\gamma+\alpha.
\]

Combining them yields

\[
0\ge(a^2-1)\gamma+(a+1)\alpha,
\]

which is impossible for \(a\ge1\), \(\gamma\ge0\), \(\alpha>0\). Therefore \(\alpha=0\), and both gaps in (6) vanish. This proves the reversed claim.

The proof directly resolves these two scalar certificate classes; it does not rely on the previous scalar result requiring slopes at least one, or on a solver's UNSAT status. The top-to-full connection and exact coefficient requirements are recorded in [transformed-certificate-audit.md](transformed-certificate-audit.md).
