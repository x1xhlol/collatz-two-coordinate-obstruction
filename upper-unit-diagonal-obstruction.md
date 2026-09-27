# Upper-triangular digit matrices with unit diagonals cannot start rule removal

This note excludes the forward full-system case in which all five digit matrices are upper triangular and both diagonal entries of every digit matrix are one. The boundary matrices and all offsets are arbitrary nonnegative real coefficients, with \(C_{00},D_{00}\ge1\). It does not exclude general upper-triangular digit matrices with other secondary diagonal entries.

Write
\[
[s](x,y)=\bigl(x+q_sy+h_s,\ y+k_s\bigr),
\qquad q_s,h_s,k_s\ge0,
\quad s\in\{a,b,e,f,g\}.
\]
Words compose with the leftmost symbol outermost. Assume all eleven forward rules are weak coefficientwise:

```text
ad -> d       bd -> gd
ae -> ea      af -> eb      ag -> fa
be -> fb      bf -> ga      bg -> gb
ce -> cb      cf -> caa     cg -> cab
```

**Theorem.** Every rule has zero first-coordinate offset gap. Therefore none can be strict under the full affine interpretation criterion requiring a positive first-offset gap.

## 1. The shear coefficients and secondary offsets each have two values

For a two-digit product, its upper-right matrix entry is the sum of the two shear coefficients, and its second offset is the sum of the two secondary offsets. In each of these coordinates, the six swap differences sum to zero, since every symbol occurs equally often on either side. All six differences are nonnegative, so all are zero. The `ag`, `be`, and `af` equalities give
\[
q_a=q_b=x,\qquad q_e=q_f=q_g=y,
\]
and
\[
k_a=k_b=r,\qquad k_e=k_f=k_g=u.
\tag{1}
\]

The upper-right entry of \(M_f-M_a^2\) is \(y-2x\), and all its other entries are zero. Hence the first row of the matrix inequality for `cf -> caa` gives
\[
C_{00}(y-2x)\ge0,
\qquad\text{so}\qquad y\ge2x.
\tag{2}
\]
The second-offset inequality for `bd -> gd` gives
\[
r\ge u.
\tag{3}
\]

## 2. Every cross term vanishes

The first offset of a two-digit word \(st\) is
\[
h_s+h_t+q_sk_t.
\]
For every swap rule the cross term on its left is \(xu\), and the cross term on its right is \(yr\). Summing all six first-offset differences cancels the \(h\)-terms and gives
\[
6(xu-yr)\ge0.
\]
Thus \(xu\ge yr\). But (2) and (3) imply
\[
yr\ge2xr\ge2xu.
\]
Nonnegativity consequently forces
\[
xu=yr=xr=yu=0.
\tag{4}
\]
These are all possible digit products \(q_sk_t\), so every such cross term vanishes.

The six swap first-offset inequalities now reduce to additive inequalities in the \(h\)-values. Their sum is zero, hence each is an equality. Again using `ag`, `be`, and `af`, we obtain
\[
h_a=h_b=R,\qquad h_e=h_f=h_g=U,
\qquad R,U\ge0.
\tag{5}
\]

## 3. The boundary and dynamic inequalities eliminate the remaining gaps

Let
\[
\kappa=C_{01}/C_{00}\ge0,
\qquad \tau=(v_d)_1\ge0,
\]
where \(v_d\) is the offset vector of the boundary symbol \(d\). No other entry of either boundary matrix is restricted or normalized.

The first-offset inequality for `bd -> gd` is
\[
R-U\ge(y-x)\tau\ge0.
\tag{6}
\]
The first-offset inequality for `ce -> cb`, divided by \(C_{00}>0\), is
\[
U-R\ge\kappa(r-u)\ge0.
\tag{7}
\]
Thus \(R=U\), and \((y-x)\tau=0\).

The first-offset inequality for `cf -> caa`, using \(xr=0\), is
\[
U-2R+\kappa(u-2r)\ge0.
\]
Since \(R=U\) and \(u\le r\), its left-hand side is at most \(-R-\kappa r\). Hence
\[
R=U=0,\qquad \kappa r=\kappa u=0.
\tag{8}
\]
Also \(y\ge2x\) and \((y-x)\tau=0\) give \(x\tau=y\tau=0\).

The two dynamic first-offset gaps are
\[
x\tau+R,\qquad (x-y)\tau+R-U,
\]
so both vanish. The three boundary first-offset gaps, divided by \(C_{00}\), are
\[
U-R+\kappa(u-r),\qquad
U-2R-xr+\kappa(u-2r),\qquad
U-2R-xr+\kappa(u-2r).
\]
They all vanish by (4) and (8). All six swap first-offset gaps were already zero. This proves the theorem.

The proof uses only unbounded nonnegative real coefficient inequalities. It requires no solver result, no finite coefficient search, and no triangular assumption on the boundary matrices. The general upper-triangular case with varying secondary diagonal entries remains outside its scope.
