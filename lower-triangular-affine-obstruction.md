# Lower-triangular two-coordinate affine interpretations cannot start rule removal

This note completes the forward full-system case in which all five digit matrices are lower triangular and their first diagonal entries are one. The boundary matrices may be arbitrary nonnegative matrices with first diagonal entries at least one. All coefficients may be arbitrary nonnegative **real** numbers.

The result is conditional on this matrix shape. The reductions to common triangular digit matrices and then to first diagonal entries equal to one are separate results. No conclusion about upper-triangular digits is used here.

## Statement and notation

For each digit symbol \(s\in\{a,b,e,f,g\}\), write
\[
[s](x,y)=\bigl(x+h_s,\ q_sx+z_sy+k_s\bigr),
\qquad h_s,q_s,z_s,k_s\ge0.
\tag{1}
\]
The two boundary symbols \(c,d\) have arbitrary nonnegative affine interpretations. Write the first row of the matrix of \(c\) as
\[
(c_0,c_1),\qquad c_0\ge1,\quad c_1\ge0.
\]
Let \(D\) be the matrix of \(d\), with \(D_{00}\ge1\), and let its offset vector be \((h_d,k_d)\).

Words compose with the leftmost symbol outermost. All eleven rules are required to be weak coefficientwise inequalities, in both the matrix and offset parts:

```text
ad -> d       bd -> gd
ae -> ea      af -> eb      ag -> fa
be -> fb      bf -> ga      bg -> gb
ce -> cb      cf -> caa     cg -> cab
```

**Theorem.** Under these hypotheses, every rule has zero difference in the first coordinate of its offset vector. Consequently no rule can be strict under the full affine interpretation criterion requiring a positive first-offset gap. This holds without any upper bound or integrality assumption on the coefficients.

## 1. The first-coordinate offsets have only two values

The first row of every digit matrix is \((1,0)\). Thus for a two-digit word the first offset is the sum of the two digit first offsets. The six swap first-offset differences have sum zero: each digit occurs equally often on the left and on the right. Every difference is nonnegative, so every difference is zero. The relations for `ag`, `be`, and `af` then give
\[
h_a=h_b=r,\qquad h_e=h_f=h_g=u,
\qquad r,u\ge0. \tag{2}
\]
The first-offset inequality for `bd -> gd` gives
\[
r\ge u. \tag{3}
\]
All swap first-offset gaps are already zero. The two dynamic first-offset gaps are \(r\) and \(r-u\).

If \(c_1=0\), the first-offset inequality for `cf -> caa` is simply
\[
c_0(u-2r)\ge0.
\]
Together with (3), this forces \(r=u=0\). Every boundary first-offset gap is then zero as well. Thus the theorem holds when \(c_1=0\).

For the rest of the proof assume \(c_1>0\), and set
\[
\lambda=c_0/c_1>0.
\]

## 2. A scalar lemma controls the lower-left coefficients

We use the following consequence of [scalar-top-obstruction.md](scalar-top-obstruction.md).

**Scalar lemma.** Suppose the same eleven forward rules are weak for nonnegative scalar affine maps
\[
\psi_s(y)=z_sy+v_s\quad(s=a,b,e,f,g),
\qquad\psi_c(y)=y,\qquad\psi_d(y)=\delta\ge0.
\]
Then all three scalar boundary constant gaps are zero. Moreover, either all five digit constants \(v_s\) are zero, or all five digit slopes are zero and all five digit constants are equal to one positive value.

The zero-gap assertion is the forward theorem in that note. For the stronger dichotomy, its proof first gives either positive binary slopes or both binary slopes zero. In the positive case every digit constant vanishes. In the zero-binary case all digit constants are equal to a value \(v\). If \(v>0\), the weak constant inequalities for `ae`, `ag`, and `bf` give, respectively,
\[
v\ge z_ev+v,\qquad
v\ge z_fv+v,\qquad
v\ge z_gv+v,
\]
forcing all three ternary slopes to vanish too. This proves the stated dichotomy.

We now apply the lemma to the lower-left coefficients \(q_s\). Associate to each digit matrix its scalar affine map
\[
\psi_s(y)=z_sy+q_s.
\tag{4}
\]
Multiplication of lower-triangular matrices of the form in (1) has lower row
\[
\bigl(q_s+z_sq_t,\ z_sz_t\bigr).
\]
Therefore the six swap matrix inequalities are precisely the scalar swap inequalities for (4).

Every digit product has first row \((1,0)\). For each boundary matrix difference, multiplication by the first row \((c_0,c_1)\) of \(C\) consequently gives \(c_1\) times its lower-row difference. Since \(c_1>0\), the three original boundary matrix inequalities imply
\[
\psi_e\ge\psi_b,\qquad
\psi_f\ge\psi_a\circ\psi_a,\qquad
\psi_g\ge\psi_a\circ\psi_b
\]
coefficientwise. These are exactly the scalar boundary inequalities with \(\psi_c\) the identity.

Finally put \(\delta=D_{10}/D_{00}\ge0\). The lower-left entries of the two dynamic matrix inequalities give
\[
q_a+(z_a-1)\delta\ge0,
\qquad
q_b-q_g+(z_b-z_g)\delta\ge0.
\]
These are the scalar dynamic inequalities with \(\psi_d(y)=\delta\); their slope inequalities are both automatic because \(\psi_d\) is constant.

All eleven scalar inequalities therefore hold. The lemma yields exactly two possibilities:

1. Every \(q_s=0\).
2. Every \(q_s=v>0\), and every \(z_s=0\).

We treat them separately.

## 3. All lower-left coefficients vanish

Suppose \(q_s=0\) for every digit. The second-coordinate offsets then compose independently of the first coordinate. Associate scalar maps
\[
\theta_s(y)=z_sy+k_s,\qquad
\theta_c(y)=y,\qquad\theta_d(y)=k_d.
\tag{5}
\]
The six scalar swap inequalities follow from the original second-offset and matrix inequalities. The scalar dynamic constant inequalities follow from the original second-offset dynamic inequalities, since the terms \(q_sh_d\) vanish. Their slope inequalities are again automatic for constant \(\theta_d\).

It remains to check the scalar boundary constants. Define their three gaps by
\[
\begin{aligned}
\Delta_e&=k_e-k_b,\\
\Delta_f&=k_f-(1+z_a)k_a,\\
\Delta_g&=k_g-k_a-z_ak_b.
\end{aligned}
\]
The actual first-offset boundary inequalities are
\[
\begin{aligned}
c_1\Delta_e&\ge c_0(r-u),\\
c_1\Delta_f&\ge c_0(2r-u),\\
c_1\Delta_g&\ge c_0(2r-u).
\end{aligned} \tag{6}
\]
All three right-hand sides are nonnegative by (3). Hence \(\Delta_e,\Delta_f,\Delta_g\ge0\), which are the remaining scalar constant inequalities. The scalar boundary slope inequalities were already obtained from the original boundary matrix inequalities in section 2.

Thus all eleven rules are weak for (5). The scalar lemma gives
\[
\Delta_e=\Delta_f=\Delta_g=0.
\]
The middle inequality in (6) then forces \(2r-u\le0\). Together with \(r\ge u\ge0\), this gives \(r=u=0\).

The two dynamic first-offset gaps are now zero. The three boundary first-offset gaps are zero because both their first-coordinate contributions and their \(\Delta\) contributions vanish. The six swap gaps were already zero. This proves the theorem in this case.

## 4. All lower-left coefficients are equal and positive

Suppose instead \(q_s=v>0\), \(z_s=0\) for every digit. The second-offset inequality for `ag -> fa` is
\[
vu+k_a\ge vr+k_f,
\qquad\text{or}\qquad
k_a-k_f\ge v(r-u).
\tag{7}
\]
The offset of `aa` is \((2r,vr+k_a)\). Consequently the first-offset inequality for `cf -> caa` is
\[
k_f-k_a\ge vr+\lambda(2r-u).
\tag{8}
\]
Adding (7) and (8) gives
\[
0\ge(v+\lambda)(2r-u).
\]
Here \(v+\lambda>0\) and \(2r-u\ge r\ge0\), so again \(r=u=0\).

All cross terms \(q_sh_t\) in the digit second-offset inequalities now vanish. The swap and boundary inequalities give
\[
k_a\ge k_e\ge k_b\ge k_g\ge k_a,
\qquad k_a\ge k_f\ge k_a.
\]
Thus all five secondary offsets are equal. Since every secondary slope is zero, the three boundary secondary-offset gaps are zero. Their actual first-offset gaps are therefore zero, as are both dynamic gaps and all six swap gaps.

This completes the proof in every lower-triangular case.

## Scope

Only necessary weak coefficient inequalities and the first-coordinate strictness requirement are used. The boundary matrices and offsets were not assumed triangular or diagonal. The argument uses neither a finite coefficient search nor a numerical solver.

This theorem excludes a first full-system rule-removal step for the stated lower-triangular class. It does not independently exclude upper-triangular digits, top interpretations, or higher-dimensional certificates.
