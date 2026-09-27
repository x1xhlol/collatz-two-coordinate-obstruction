# Exact boundary normalization for the remaining upper case

The earlier [aggregate](aggregate-matrix-obstruction.md) and
[diagonal](triangular-first-diagonal.md) results reduce every forward full
two-coordinate candidate to compatible triangular digit matrices with
first diagonal entry one. The
[lower affine case](lower-triangular-affine-obstruction.md) is excluded.
This note gives an equivalent existence problem for the remaining upper
case; it does not solve that problem.

Write each digit interpretation, for \(s\in\{a,b,e,f,g\}\), as

\[
F_s(x,y)=\bigl(x+q_sy+h_s,\ z_sy+k_s\bigr),
\qquad q_s,z_s,h_s,k_s\ge0.
\tag{1}
\]

The original boundary maps \(C,D\) may be arbitrary nonnegative affine
maps with \(C_{00},D_{00}\ge1\). All comparisons are coefficientwise,
and a strict rule has a positive first-offset gap. A common rescaling of
all affine offsets converts any selected positive gap into a unit gap.

## Normalized boundaries

Set

\[
\kappa=C_{01}/C_{00}\ge0,\qquad \tau=(v_d)_1\ge0.
\]

Replace the boundary interpretations by

\[
\widehat C(x,y)=(x+\kappa y,0),\qquad
\widehat D(x,y)=(x,\tau).
\tag{2}
\]

Keep all five digit interpretations unchanged. Both new boundary matrices
have first diagonal entry one and all their coefficients are nonnegative.

Every B-rule has the form \(c\ell\to cr\). Its original first-row
matrix difference and first-offset difference are, respectively,

\[
(C_{00},C_{01})(M_\ell-M_r),\qquad
(C_{00},C_{01})(v_\ell-v_r).
\]

The boundary offset cancels. Under (2), these differences are divided
by the positive number \(C_{00}\); the new second-row and second-offset
differences are zero. Thus all B-rules remain weak, and every positive
first-offset B-gap remains positive.

All digit matrices in (1) fix the first coordinate vector \(e_0\).
Consequently both dynamic matrix comparisons become equalities after
replacing \(D\) by (2). Their offset differences are unchanged:

\[
\begin{aligned}
ad-d:&\quad(q_a\tau+h_a,\ (z_a-1)\tau+k_a),\\
bd-gd:&\quad((q_b-q_g)\tau+h_b-h_g,\
                   (z_b-z_g)\tau+k_b-k_g).
\end{aligned}
\]

The original first coordinate \((v_d)_0\) cancels because every digit
has first diagonal entry one. The original matrix of \(D\) does not
enter these offset expressions. The six swap comparisons are unchanged.

Therefore the replacement preserves all eleven weak comparisons and the
sign of every first-offset gap. Conversely, the normalized maps are
themselves admissible full interpretations. Existence of an upper
certificate is thus equivalent to existence in the **22 nonnegative
parameters** \(q_s,z_s,h_s,k_s,\kappa,\tau\). This is not an assertion
that a certificate exists.

## Exact reduced constraints

For a digit word \(w\), write its interpretation in the form (1), using
coefficients \(q_w,z_w,h_w,k_w\). Concatenation obeys

\[
\begin{aligned}
q_{uv}&=q_v+q_uz_v,&z_{uv}&=z_uz_v,\\
h_{uv}&=h_u+h_v+q_uk_v,&k_{uv}&=k_u+z_uk_v.
\end{aligned}
\tag{3}
\]

For every swap \(\ell\to r\), all four differences
\(q_\ell-q_r,z_\ell-z_r,h_\ell-h_r,k_\ell-k_r\) must be
nonnegative. Its first strict gap is \(h_\ell-h_r\).

The dynamic constraints and their strict first gaps are exactly the two
displayed vectors above. For each B-rule \(c\ell\to cr\), the two
remaining weak constraints are

\[
q_\ell+\kappa z_\ell\ge q_r+\kappa z_r,\qquad
h_\ell+\kappa k_\ell\ge h_r+\kappa k_r.
\tag{4}
\]

The second difference in (4) is its first-offset strict gap. Requiring
at least one of these eleven gaps to be positive is the unresolved first
rule-removal question. The formulas omit no weak rule.

## Homogeneous reversal correspondence

The digit homogeneous matrices are

\[
H_s=\begin{pmatrix}1&q_s&h_s\\0&z_s&k_s\\0&0&1\end{pmatrix}.
\]

Let \(J\) reverse the three homogeneous coordinates and put
\(\Phi(H)=JH^{\mathsf T}J\). Then
\(\Phi(H_uH_v)=\Phi(H_v)\Phi(H_u)\).
For digits, this exchanges \(q_s\) and \(k_s\) while keeping
\(z_s,h_s\). For the normalized boundaries, the image of the symbol
\(c\) has the form \(D(\kappa)\), and the image of the symbol \(d\)
has the form \(C(\tau)\). All seven images are again nonnegative affine
interpretations with first diagonal entry one.

Keeping the original symbol labels, \(\Phi\) converts the forward
inequalities to those for the exact word-reversed rules. Entrywise
inequalities and first-offset gaps, which occupy position \((0,2)\),
are preserved. Only the boundary *forms* exchange; the labels are not
renamed. This observation concerns the normalized family and does not
claim that arbitrary affine boundary matrices can be transposed this way.
