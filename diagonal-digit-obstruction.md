# Diagonal digit matrices cannot start full rule removal

This note concerns forward full interpretations with nonnegative real
two-coordinate affine maps and every first diagonal matrix entry at least
one. If all five **digit** matrices are diagonal, no rule can have a strict
first-offset decrease while all eleven rules remain weak. The two boundary
matrices may be arbitrary nonnegative matrices; they need not be diagonal.

The result uses the independently proved
[scalar top obstruction](scalar-top-obstruction.md). It does not exclude
general triangular digit matrices or prove Collatz.

Write each digit map as

\[
F_j(x)=\operatorname{diag}(p_j,z_j)x+(h_j,k_j)^{\mathsf T},
\qquad p_j\ge1,\quad z_j,h_j,k_j\ge0.
\]

Let the boundary matrices be \(C,D\). Their first diagonal entries are
at least one. All words are interpreted leftmost outermost.

## First-coordinate slopes and constants

The six swap matrix deficits are nonnegative and sum to a commutator.
Its trace is zero, so each individual diagonal deficit is zero. Applied
to the strictly positive first diagonal entries, the exact scalar swap
relations give

\[
p_a=p_b=t\ge1,\qquad p_e=p_f=p_g=s\ge1.
\]

The first-column comparison for \(cf\to caa\) gives \(s\ge t^2\),
because \(C_{00}>0\). The first-row comparison for \(bd\to gd\)
gives \(t\ge s\), because \(D_{00}>0\). Therefore \(t=s=1\).

Put \(h_a=\alpha,h_b=\beta,h_e=\varepsilon,
h_f=\varphi,h_g=\gamma\). The first-offset comparisons of the swaps
give

\[
\alpha+\varphi\ge\varepsilon+\beta,\qquad
\gamma\ge\varphi,\qquad\varepsilon\ge\varphi,\qquad
\beta+\varphi\ge\gamma+\alpha.
\]

Adding the first and last inequalities gives
\(2\varphi\ge\varepsilon+\gamma\). Consequently

\[
\alpha=\beta=r\ge0,\qquad
\varepsilon=\varphi=\gamma=u\ge0.
\]

The dynamic rule \(bd\to gd\) then gives \(r\ge u\).

## The second coordinate supplies a scalar top interpretation

Write the first row of \(C\) as \((c_0,c_1)\), with
\(c_0\ge1\) and \(c_1\ge0\). Define the second-coordinate B-offset
differences

\[
\begin{aligned}
L_e&=k_e-k_b,\\
L_f&=k_f-(z_a+1)k_a,\\
L_g&=k_g-z_a k_b-k_a.
\end{aligned}
\]

The actual first-offset gaps of the three B-rules are

\[
c_0(u-r)+c_1L_e,\qquad
c_0(u-2r)+c_1L_f,\qquad
c_0(u-2r)+c_1L_g.
\tag{1}
\]

If \(c_1=0\), weak orientation of the second expression, together with
\(r\ge u\ge0\), immediately forces \(r=u=0\). All three gaps vanish.

Suppose \(c_1>0\). The first terms of all expressions in (1) are
nonpositive. Weak orientation therefore implies
\(L_e,L_f,L_g\ge0\). The second-column matrix comparisons of the
B-rules similarly give

\[
z_e\ge z_b,\qquad z_f\ge z_a^2,\qquad z_g\ge z_a z_b.
\]

Consider scalar digit maps \(x\mapsto z_jx+k_j\), the scalar boundary
map \([c](x)=x\), and \([d](x)=D_{11}x+(v_d)_1\), where indices
here are zero-based. These maps are nonnegative, with slopes allowed to
be zero. Their swap inequalities are exactly the second-coordinate
inequalities of the original diagonal digit maps. Their dynamic slope
inequalities follow from the \((1,1)\) entries of the original dynamic
matrix comparisons, and their dynamic offset inequalities are the
original second-coordinate offset comparisons. Their three B-rules are
weak by the inequalities just derived.

Thus all eleven rules are weak in this scalar interpretation. The scalar
top theorem forces its three B-offset gaps to be zero:

\[
L_e=L_f=L_g=0.
\]

Returning to (1), the second weak comparison now gives \(u\ge2r\).
Together with \(r\ge u\ge0\), this forces \(r=u=0\). All B-gaps
therefore vanish in this case too.

Every digit first-coordinate map is now the identity. The two dynamic
first-offset gaps vanish, and so do all six swap first-offset gaps.
The three B-gaps were already shown to vanish. No first strict rule is
possible, which proves the claim.
