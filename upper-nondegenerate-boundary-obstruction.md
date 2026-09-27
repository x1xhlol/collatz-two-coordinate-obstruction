# Upper triangular digits with a nonzero second row in D

This note proves a restricted obstruction for the full forward rewriting system. It does **not** settle the general upper triangular case: the hypothesis on the boundary matrix of `d` is essential to the reduction below.

Write each digit interpretation as

\[
[s](x,y)=(x+q_sy+h_s,\ z_sy+k_s),
\qquad q_s,z_s,h_s,k_s\ge0,
\quad s\in\{a,b,e,f,g\}.
\]

Let both boundary symbols have arbitrary nonnegative affine interpretations with first matrix entries at least one. All eleven rules are weak coefficientwise, using leftmost-outermost composition:

```text
ad -> d       bd -> gd
ae -> ea      af -> eb      ag -> fa
be -> fb      bf -> ga      bg -> gb
ce -> cb      cf -> caa     cg -> cab
```

**Claim.** If the matrix of `d` has a nonzero second row, every rule has zero first-offset gap. Thus such an interpretation cannot start full-system rule removal. Coefficients may be arbitrary nonnegative real numbers.

## Scalar matrix reduction

Set \(\kappa=C_{01}/C_{00}\ge0\). Associate scalar maps

\[
\psi_s(y)=z_sy+q_s,\qquad
\psi_c(y)=\kappa,\qquad \psi_d(y)=y.
\]

The upper right entry of a digit product satisfies
\(q_{st}=q_t+z_tq_s\). Consequently all six swap matrix inequalities become exactly the scalar inequalities for the six **reversed** swaps. Multiplying the boundary matrix differences by the first row of \(C\), and dividing by \(C_{00}>0\), gives the three reversed scalar boundary inequalities.

The nonzero second row of \(D\) makes the dynamic matrix inequalities imply

\[
z_a\ge1,\qquad z_b\ge z_g,\qquad q_b\ge q_g.
\]

These are all the remaining scalar dynamic inequalities; \(q_a\ge0\) is already assumed. Thus all eleven reversed rules are weak in the scalar interpretation. The reversed theorem in [scalar-top-obstruction.md](scalar-top-obstruction.md) gives

\[
q_a=0,\qquad q_b=q_g.
\tag{1}
\]

## Classification of the upper right entries

Use \(a,b,e,f,g\) temporarily for the five numbers \(z_s\), and write
\(\beta=q_b=q_g\), \(\varepsilon=q_e\), \(\varphi=q_f\). The six nonnegative swap slope gaps have sum zero, so all are zero. In particular,

\[
af=eb,\qquad a(g-f)=0,\qquad b(e-f)=0,\qquad bf=ga.
\]

Since \(a\ge1\), \(g=f\). The upper right inequalities of `af`, `ag`, `ae`, and `be` include

\[
\varphi\ge\beta+b\varepsilon,\qquad
\beta\ge a\varphi,\qquad
(1-a)\varepsilon\ge0,\qquad
\varepsilon+(e-1)\beta\ge b\varphi.
\tag{2}
\]

If \(f>0\), the slope equalities give \(b=a\), \(e=f=g\le a\). If \(a>1\), the first two inequalities of (2) force \(\beta=\varphi=0\), and then \(\varepsilon=0\). If \(a=1\), those same inequalities give \(\varphi=\beta\), \(\varepsilon=0\); the last inequality, together with \(e\le1\), forces \(\beta=0\).

If \(f=0\) and \(b>0\), then \(e=g=0\). Again (2) forces all three upper right entries to vanish: for \(a>1\) use its first two inequalities; for \(a=1\) they give \(\varphi=\beta\), \(\varepsilon=0\), and its last inequality then gives \(\beta=0\).

The only remaining case has \(b=f=g=0\). If \(a>1\), (2) gives all three entries zero. If \(a=1\), it instead gives \(\varphi=\beta\). Thus either all five \(q_s\) vanish, or the digit parameters have the exceptional form

\[
z_a=1,\quad z_b=z_f=z_g=0,\quad z_e\ge0,
\qquad q_a=0,\quad q_b=q_f=q_g=\beta\ge0,
\quad q_e=\varepsilon\ge0,
\tag{3}
\]

where \(\beta+\varepsilon>0\). The boundary matrix inequalities also give

\[
\beta\ge\kappa,\qquad z_e\kappa+\varepsilon\ge\beta.
\tag{4}
\]

If all \(q_s=0\), the digit matrices are diagonal, so [diagonal-digit-obstruction.md](diagonal-digit-obstruction.md) already proves the claim. It remains to treat (3).

## Exceptional form with beta positive

Assume \(\beta>0\). The second-offset dynamic inequality for `bd` gives \(k_b\ge k_g\). The first-offset swap inequality for `bg` gives \(\beta(k_g-k_b)\ge0\). Hence

\[
k_b=k_g.
\]

The first-offset dynamic inequality also gives \(h_b\ge h_g\). The first-offset boundary inequality for `cg`, divided by \(C_{00}\), is now

\[
h_g-h_b-h_a-\kappa k_a\ge0.
\]

Therefore \(h_a=0\), \(h_g=h_b\), and \(\kappa k_a=0\). The first-offset inequalities for `af` and `ag` give

\[
h_f\ge h_e+h_b+\varepsilon k_b,
\qquad h_b\ge h_f+\beta k_a.
\]

Nonnegativity and \(\beta>0\) imply

\[
h_f=h_b,\quad h_e=0,\quad k_a=0,
\quad\varepsilon k_b=0.
\]

The second-offset inequalities for `af` and `be` imply

\[
k_b\ge k_f\ge z_ek_b+k_e,
\]

while the first-offset inequality for `be` gives

\[
\beta(k_e-k_b)\ge h_b.
\]

Together these force

\[
h_b=0,\qquad k_e=k_f=k_b=k_g,
\qquad z_ek_b=0.
\]

Since both \(\varepsilon k_b\) and \(z_ek_b\) vanish, the second inequality in (4), whose right side is positive, forces \(k_b=0\). Every digit offset consequently vanishes.

## Exceptional form with beta zero

Here \(\varepsilon>0\) and (4) gives \(\kappa=0\). The first-offset inequality for `ae` gives \(-\varepsilon k_a\ge0\), so \(k_a=0\). The inequalities for `bd` and `cg` give \(h_a=0\), \(h_g=h_b\). The inequalities for `af` and `ag` then give

\[
h_f\ge h_e+h_b+\varepsilon k_b,
\qquad h_b\ge h_f.
\]

Thus \(h_e=0\), \(h_f=h_b\), and \(k_b=0\). The second-offset inequalities for `af`, `be`, and `bd` now force \(k_e=k_f=k_g=0\). Finally the first-offset boundary inequality for `ce` is \(-h_b\ge0\), so every digit offset again vanishes.

In either exceptional subcase, (1) makes both dynamic first-offset gaps zero. All digit offsets are zero, so all swap and boundary first-offset gaps are also zero. This proves the claim.

## Remaining case

The proof does not cover \(D_{10}=D_{11}=0\). Indeed [upper-boundary-normalization.md](upper-boundary-normalization.md) reduces the unrestricted upper triangular certificate problem to a boundary of exactly that form. No full upper triangular obstruction is asserted here.
