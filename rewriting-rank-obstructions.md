# Scalar and structured-matrix obstructions for the mixed-base system

This note rules out particular interpretation certificates. It does not prove termination or nontermination of the Collatz rewriting system, and does not rule out unrestricted two-coordinate matrix interpretations.

## 1. System and certificate convention

Use the authors' ASCII names: \(a,b\) are binary digits, \(e,f,g\) ternary digits, and \(c,d\) the left and right boundaries. The full system is
\[
\begin{array}{lll}
ad\to d,&bd\to gd,\\
ae\to ea,&af\to eb,&ag\to fa,\\
be\to fb,&bf\to ga,&bg\to gb,\\
ce\to cb,&cf\to caa,&cg\to cab.
\end{array} \tag{1}
\]
These are the mixed-base rules of Yolcu–Aaronson–Heule, section 3.2. Their Theorems 3.8 and 3.10 rule out natural matrix proofs for the **unary** encoding, including the specified dependency-pair setting; those theorems do not cover (1). [Paper](https://emreyolcu.com/research/rewriting-collatz.pdf), [exact rule file](https://raw.githubusercontent.com/emreyolcu/rewriting-collatz/main/rules/collatz-T.srs).

For natural affine matrix interpretations, write
\[
[\sigma](x)=M_\sigma x+v_\sigma,
\qquad [uv]=[u]\circ[v].
\]
The full monotone convention has nonnegative integer coefficients and \((M_\sigma)_{11}\ge1\). A weak rule requires \(M_\ell\ge M_r\) and \(v_\ell\ge v_r\) entrywise; a strict rule additionally requires \((v_\ell)_1>(v_r)_1\). These are the authors' implemented natural-certificate conditions. [Natural interpretation implementation](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/prover/natural.py).

The issue considered below is whether all rules can be weak while at least one is strict, allowing the first step of rule removal.

## 2. Complete scalar-affine constraints

Let
\[
[\sigma](x)=\lambda_\sigma x+\beta_\sigma,
\qquad \lambda_\sigma\ge1,\quad\beta_\sigma\ge0.
\]
We allow real coefficients here, making the obstruction stronger than the natural-integer version. The following table gives the exact weak constraints after cancelling positive boundary slopes and other common positive factors. Each row requires both columns.

| Rule | Slope constraint | Constant constraint |
|---|---|---|
| \(ad\to d\) | \(\lambda_a\ge1\) | \((\lambda_a-1)\beta_d+\beta_a\ge0\) |
| \(bd\to gd\) | \(\lambda_b\ge\lambda_g\) | \((\lambda_b-\lambda_g)\beta_d+\beta_b\ge\beta_g\) |
| \(ae\to ea\) | automatic | \(\lambda_a\beta_e+\beta_a\ge\lambda_e\beta_a+\beta_e\) |
| \(af\to eb\) | \(\lambda_a\lambda_f\ge\lambda_e\lambda_b\) | \(\lambda_a\beta_f+\beta_a\ge\lambda_e\beta_b+\beta_e\) |
| \(ag\to fa\) | \(\lambda_g\ge\lambda_f\) | \(\lambda_a\beta_g+\beta_a\ge\lambda_f\beta_a+\beta_f\) |
| \(be\to fb\) | \(\lambda_e\ge\lambda_f\) | \(\lambda_b\beta_e+\beta_b\ge\lambda_f\beta_b+\beta_f\) |
| \(bf\to ga\) | \(\lambda_b\lambda_f\ge\lambda_g\lambda_a\) | \(\lambda_b\beta_f+\beta_b\ge\lambda_g\beta_a+\beta_g\) |
| \(bg\to gb\) | automatic | \(\lambda_b\beta_g+\beta_b\ge\lambda_g\beta_b+\beta_g\) |
| \(ce\to cb\) | \(\lambda_e\ge\lambda_b\) | \(\beta_e\ge\beta_b\) |
| \(cf\to caa\) | \(\lambda_f\ge\lambda_a^2\) | \(\beta_f\ge(\lambda_a+1)\beta_a\) |
| \(cg\to cab\) | \(\lambda_g\ge\lambda_a\lambda_b\) | \(\beta_g\ge\lambda_a\beta_b+\beta_a\) |

For a scalar rule to be strict on all \(x\ge0\), its constant inequality must be strict as well as its slope inequality being weak. The five-rule argument below already makes that impossible.

## 3. Five weak rules force every digit map to be the identity

Only these five rules are needed:
\[
bd\to gd,\quad af\to eb,\quad ag\to fa,
\quad ce\to cb,\quad cg\to cab. \tag{2}
\]
Their slope constraints give
\[
\lambda_b\ge\lambda_g\ge\lambda_a\lambda_b.
\]
Since \(\lambda_a,\lambda_b\ge1\), this forces
\[
\lambda_a=1,\qquad\lambda_g=\lambda_b.
\]
The other three slope inequalities then give
\[
\lambda_b\ge\lambda_f
\ge\lambda_e\lambda_b
\ge\lambda_b^2.
\]
Therefore
\[
\boxed{\lambda_a=\lambda_b=\lambda_e=\lambda_f=\lambda_g=1.} \tag{3}
\]

With those slopes equal to one, the same five constant constraints reduce to
\[
\beta_b\ge\beta_g\ge\beta_a+\beta_b,
\qquad
\beta_g\ge\beta_f\ge\beta_e+\beta_b,
\qquad
\beta_e\ge\beta_b.
\]
Nonnegativity first gives \(\beta_a=0\) and \(\beta_g=\beta_b\). It then gives \(\beta_e=0\), followed by \(\beta_b=\beta_f=\beta_g=0\). Thus
\[
\boxed{[a]=[b]=[e]=[f]=[g]=\mathrm{id}.} \tag{4}
\]

The two boundary maps can remain arbitrary monotone scalar affine maps. Nevertheless, after (4), both sides of every rule in (1) have exactly the same interpretation. Consequently:

> No monotone scalar affine interpretation can weakly orient all rules of the full mixed-base system and strictly orient even one rule.

In particular, a sequence of scalar rule-removal certificates cannot start on the full system. This obstruction does not say that every proper subsystem lacks a scalar certificate.

## 4. Reversal does not evade this scalar obstruction

Reversing every word in (1) leaves all scalar slope constraints unchanged because scalar multiplication commutes. Thus the same five reversed rules force (3).

After that collapse, their offset comparisons are again exactly those used above: some have a common positive boundary multiplier, which can be cancelled. They force (4) again. Therefore the scalar obstruction applies to the reversed full system as well.

This also rules out the \(2\times2\) homogeneous matrices
\[
\begin{pmatrix}\lambda_\sigma&\beta_\sigma\\0&1\end{pmatrix}
\]
that merely encode a single scalar affine map. Such matrices should not be confused with genuine two-coordinate affine interpretations \(x\mapsto M_\sigma x+v_\sigma\), whose homogeneous encoding has size \(3\times3\).

## 5. A common positive projection also rules out matrix certificates

The scalar argument extends to any dimension under a precise structural condition.

**Projection obstruction.** Suppose a natural matrix interpretation has a common nonnegative left eigenvector \(w\) satisfying
\[
w_1>0,
\qquad w^{\mathsf T}M_\sigma=\lambda_\sigma w^{\mathsf T}
\quad\text{for every symbol }\sigma.
\tag{5}
\]
Then it cannot weakly orient the full system and strictly orient any rule.

To prove this, first observe
\[
\lambda_\sigma w_1
=\sum_i w_i(M_\sigma)_{i1}
\ge w_1(M_\sigma)_{11}\ge w_1,
\]
so \(\lambda_\sigma\ge1\). Let \(\beta_\sigma=w^{\mathsf T}v_\sigma\ge0\). Composition projects to the scalar affine maps
\[
z\longmapsto\lambda_\sigma z+\beta_\sigma.
\]
Entrywise weak matrix and vector inequalities imply the corresponding scalar inequalities. A strict first-coordinate constant inequality projects to a strict scalar one because \(w_1>0\) and all coordinate differences are nonnegative. This contradicts sections 3–4.

The obstruction covers, in particular:

* diagonal matrices in any dimension;
* matrices whose first row has no off-diagonal entries, including consistently lower-triangular matrices, by taking \(w=e_1\);
* pairwise commuting nonnegative matrices when at least one is irreducible. Its positive left Perron eigenvector is common to the commuting family, so (5) holds.

The last assertion uses the simple Perron eigenspace of an irreducible nonnegative matrix: multiplying its positive left eigenvector by a commuting matrix stays in that eigenspace. The multiplier is nonzero because \((M_\sigma)_{11}\ge1\).

In two coordinates this projection condition is an explicit algebraic test. Write
\[
M_\sigma=\begin{pmatrix}p_\sigma&q_\sigma\\r_\sigma&s_\sigma\end{pmatrix}.
\]
A common vector \(w=(1,\tau)\), with \(\tau\ge0\), exists exactly when the quadratics
\[
r_\sigma\tau^2+(p_\sigma-s_\sigma)\tau-q_\sigma=0
\tag{6}
\]
have a common nonnegative solution for all seven symbols. Any full-system natural certificate must therefore avoid such a solution. This is a necessary condition, not a sufficiency claim.

## 6. What is not excluded in two coordinates

For general nonnegative \(2\times2\) matrices, the first entry of a product is
\[
(MN)_{11}=M_{11}N_{11}+M_{12}N_{21}.
\]
The extra term prevents the scalar cancellation argument. For example,
\[
M=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
N=\begin{pmatrix}1&0\\1&1\end{pmatrix}
\]
both satisfy the natural monotonicity condition, but \((MN)_{11}=2\) and \((NM)_{11}=1\). Treating their first diagonal entries as scalar slopes would lose exactly this information.

No analytic impossibility theorem for all such two-coordinate affine interpretations is established here. Nor is a successful full-system certificate supplied. A general candidate still must satisfy the exact composition inequalities
\[
M_{uv}=M_uM_v,
\qquad v_{uv}=M_uv_v+v_u
\]
for all eleven rules, with an actual strict first-coordinate constant decrease in at least one rule. It must escape the common-projection obstruction (5).

Weak orientation alone does not force that common projection. Set all five digit maps to the identity, all offsets to zero, and, for example, set the boundary matrices to
\[
M_c=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
M_d=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
\]
Every rule is then an equality. But \(M_c\) has no nonnegative left eigenvector with positive first coordinate: its first coordinate would force eigenvalue one, and its second would then force the first coordinate to vanish. Thus a proof that all weak full-system interpretations have the structure (5) is false. The example has no strict rule and is not a termination certificate.

There is a useful restriction on the two commutator inequalities. If \(P,Q\) are nonnegative matrices, \(PQ\ge QP\) entrywise, and either matrix is irreducible, then
\[
PQ=QP. \tag{7}
\]
For example, if \(P\) is irreducible, take its positive left and right Perron eigenvectors \(u,v\). Then
\[
u^{\mathsf T}(PQ-QP)v=0.
\]
Every term is nonnegative, and every weight \(u_i v_j\) is positive, so the commutator vanishes entrywise. The proof with \(Q\) irreducible is the same.

Applied to the full rule constraints, (7) forces \(M_aM_e=M_eM_a\) whenever either \(M_a\) or \(M_e\) is irreducible, and similarly forces \(M_bM_g=M_gM_b\) whenever either member of that pair is irreducible. In two coordinates, irreducibility means that both off-diagonal entries are positive. This restriction concerns the matrix parts; it neither forces their affine offsets to commute nor licenses cancellation through the boundary matrices. It does not complete the arbitrary two-coordinate obstruction.

These conclusions concern full monotone interpretations. They do not automatically apply to top termination or dependency-pair settings that permit zero scalar slopes or relax monotonicity of some symbols. Arctic interpretations also use different algebraic operations and are outside this scalar-affine argument.

## Scope of the result

There is a complete analytic obstruction to the first scalar-affine rule-removal step for the mixed-base system, already forced by five rules. The same proof excludes substantial structured classes of matrix interpretations. The unrestricted mixed-base matrix-certificate problem remains unresolved by these arguments; the paper's unary impossibility theorem cannot be substituted for that missing result.
