# Reversed triangular affine interpretations

This note concerns the exact word-reversed system, with leftmost-outermost
composition:

```text
da -> d       db -> dg
ea -> ae      fa -> be      ga -> af
eb -> bf      fb -> ag      gb -> bg
ec -> bc      fc -> aac     gc -> bac
```

Every symbol has a nonnegative real affine interpretation whose first
matrix entry is at least one. All eleven rules are weak coefficientwise;
strictness requires a positive first-offset gap. The earlier
[aggregate](aggregate-matrix-obstruction.md) and
[first-diagonal](triangular-first-diagonal.md) theorems apply in this
orientation too: the five digit matrices share an upper or lower
triangular orientation, and each first diagonal entry is one.

## Reversed upper models reduce to forward upper models

Write the upper digit maps as

\[
F_s(x,y)=(x+q_sy+h_s,\ z_sy+k_s).
\]

Let \(C,D\) be arbitrary admissible boundary maps. Set
\(\lambda=D_{01}/D_{00}\) and \(\sigma=(v_c)_1\), and replace them by

\[
\widehat D(x,y)=(x+\lambda y,0),\qquad
\widehat C(x,y)=(x,\sigma).
\tag{1}
\]

The two reversed dynamic rules have the common outer symbol \(d\).
Their first-row matrix and first-offset differences are divided by
\(D_{00}>0\), and their new second-coordinate differences are zero.
Thus their weak inequalities and first-offset gap signs are preserved.

The three reversed boundary rules have the common inner symbol \(c\).
All digit matrices fix the first basis vector, so their matrix differences
become zero under (1). Their offset differences are unchanged: the
original first offset of \(c\) cancels, and its second offset remains
\(\sigma\). The swap rules are unchanged. The replacement therefore
preserves every weak rule and every first-offset gap sign.

For homogeneous matrices put \(\Phi(H)=JH^{\mathsf T}J\), where \(J\)
reverses the three coordinates. As shown in
[the forward normalization note](upper-boundary-normalization.md), this
map reverses products, preserves coefficientwise inequalities and the
first-offset entry, and exchanges digit parameters \(q_s,k_s\).
Under (1), all its images are nonnegative affine maps: the symbol \(c\)
gets the forward boundary form \((x+\sigma y,0)\), and the symbol \(d\)
gets \((x,\lambda)\). The labels are unchanged.

Hence any strict reversed upper model would give a strict forward upper
model. This is an exact reduction, with no bound on coefficients.

## Reversed lower models cannot have a strict gap

Now write

\[
F_s(x,y)=(x+h_s,\ q_sx+z_sy+k_s).
\tag{2}
\]

The sum of the six swap first-offset gaps is zero. Each is nonnegative,
so each is zero. Their additive equalities give

\[
h_a=h_b=r,\qquad h_e=h_f=h_g=u.
\]

The first-offset inequalities for the three reversed boundary rules give
\(u\ge2r\ge0\). If \(D_{01}=0\), the first-offset dynamic comparison
`db -> dg` gives \(r\ge u\), hence \(r=u=0\). All first-offset gaps
then vanish. Suppose from now on that \(D_{01}>0\).

### Scalar matrix constraints

The first row of the two dynamic matrix comparisons implies

\[
z_a\ge1,\qquad z_b\ge z_g,\qquad q_b\ge q_g.
\tag{3}
\]

Set \(\kappa=C_{10}/C_{00}\). The scalar digit maps
\(\psi_s(y)=z_sy+q_s\), with \(\psi_c(y)=\kappa\) and
\(\psi_d(y)=y\), weakly orient all eleven reversed rules. For the
swaps this follows from lower-triangular matrix multiplication; for the
three boundary rules it follows from the second-row, first-column matrix
comparisons divided by \(C_{00}>0\). Conditions (3) give the dynamic
comparisons.

The [scalar reversed theorem](scalar-top-obstruction.md) therefore gives
\(q_a=0\) and \(q_b=q_g\). The scalar classification in
[the nonzero-boundary-row proof](upper-nondegenerate-boundary-obstruction.md),
which uses only these scalar matrix constraints, gives two possibilities:

1. All five \(q_s\) are zero.
2. The exceptional parameters satisfy
   \[
   z_a=1,\quad z_b=z_f=z_g=0,\quad
   q_a=0,\quad q_b=q_f=q_g=\beta\ge0,
   \]
   with \(z_e,q_e\ge0\) and \(\beta+q_e>0\).

### All lower-left entries zero

The dynamic first-offset comparison is

\[
D_{00}(r-u)+D_{01}(k_b-k_g)\ge0.
\tag{4}
\]

Since \(u\ge2r\), this implies \(k_b\ge k_g\). Consider the scalar
maps \(\theta_s(y)=z_sy+k_s\),
\(\theta_c(y)=C_{11}y+(v_c)_1\), and \(\theta_d(y)=y\).
All reversed swaps and boundary rules are weak by the second-coordinate
comparisons of the original affine model, since every \(q_s=0\).
The dynamic rules are weak by (3), \(k_a\ge0\), and \(k_b\ge k_g\).
The scalar reversed theorem gives

\[
k_a=0,\qquad k_b=k_g.
\]

Equation (4) now implies \(r\ge u\), so \(r=u=0\). Both dynamic
first-offset gaps are zero, and so are all swap and boundary first-offset
gaps.

### Exceptional lower-left entries

The second-offset inequality for `gb -> bg` becomes

\[
k_g-k_b+\beta(r-u)\ge0.
\]

Thus \(k_g\ge k_b\), because \(u\ge2r\). In (4) both summands are
nonpositive. Consequently \(r=u=0\) and \(k_b=k_g\).

All terms \(q_sh_t\) now vanish. The second-offset inequalities for
`fa -> be` and `ga -> af` reduce to

\[
k_f\ge k_b,\qquad k_g\ge k_a+k_f.
\]

Since \(k_g=k_b\), these force \(k_a=0\). The first-offset gaps of
`da -> d` and `db -> dg` are respectively
\(D_{00}r+D_{01}k_a=0\) and the expression in (4), also zero.
The other nine first-offset gaps already vanish. This proves the lower
obstruction, including zero coefficients and arbitrary admissible
boundary matrices and offsets.

The lower obstruction and the upper reduction concern a certificate
class. They do not establish convergence of Collatz orbits.
