# Transformed certificates for the full mixed-base Collatz system

The simplest audited transformed target is **relative top termination of the three boundary rules against all eleven original rules**. A complete certificate for this target implies the full Collatz conjecture. It permits nonnegative affine matrices with zero first diagonal entries, unlike full-context strict interpretations.

The source is Yolcu–Aaronson–Heule, [author paper](https://emreyolcu.com/research/rewriting-collatz.pdf), especially Theorem 2.15, Lemmas 3.15–3.18, and Section 4.3. All repository links below are pinned to commit `8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340`. The audit concerns the mixed-base system T, not the unary system Z.

## 1. Exact target and complete implication chain

Use the eleven canonical rules in [rewriting-source-audit.md](rewriting-source-audit.md). Write

```text
D = {ad -> d, bd -> gd}
B = {ce -> cb, cf -> caa, cg -> cab}
A = {ae -> ea, af -> eb, ag -> fa, be -> fb, bf -> ga, bg -> gb}
T = D union A union B;  X = A union B.
```

For the proposed certificate, every rule of T remains weak. The distinguished strict rules are

```text
ce |-> cb
cf |-> caa
cg |-> cab
```

The arrow `|->` means replacement at the left end only: `left + suffix` becomes `right + suffix`, with no prefix. The obligation is SN(B_top / T). Keeping all eleven weak rules explicitly avoids ambiguity about ordinary occurrences of a distinguished rule.

The complete chain is

\[
\mathrm{SN}(B_{\rm top}/T)
\Longrightarrow \mathrm{SN}(B/T)
\Longrightarrow \mathrm{SN}(T)
\Longleftrightarrow \text{positive Collatz convergence}.
\]

The first implication is Lemma 3.18(1); the second uses termination of T\B and rule removal; the last is Theorem 3.17. Here is an independent proof of the delicate lifting step.

Every rule preserves the sequence of boundary symbols `c,d`. Thus a word has finitely many fixed digit blocks between consecutive boundaries, and different blocks evolve independently. A B-step belongs to the block immediately after its `c`. A block with no right boundary `d` has no D-steps; it terminates because X terminates. Consequently, infinitely many occurrences of any chosen B-subset must occur in a block bounded by `c` on the left and `d` on the right. Restricting to the rewrites of that block yields an infinite canonical derivation `c...d` in which the selected B-rules occur infinitely often. Within this block every B-step is a top step. A relative top certificate forbids this. This proof also applies after deleting previously removed rules.

The auxiliary termination claims are elementary. For X, B decreases the number of ternary digits; after the last B-step, A decreases the number of binary-before-ternary pairs. For T\B, D consumes a binary digit, while A preserves their number; after finitely many D-steps only the terminating A-system remains. These arguments apply to arbitrary words.

An alternative target reverses every word and distinguishes the two top rules `da |-> d`, `db |-> dg`, retaining all reversed T-rules weak. Lemma 3.18(2) lifts their relative top termination to full relative termination. Their residual system is X reversed, which terminates. Either complete target is sufficient.

## 2. Exact matrix conditions for the top target

Natural affine interpretations use \(F_s(x)=M_sx+v_s\) on \(\mathbb N^k\), nonnegative integer entries, and leftmost-outermost composition. **No condition \((M_s)_{00}\ge1\) is needed.** Nonnegative entries preserve componentwise weak comparisons inside arbitrary prefixes. Strict comparisons are required only at the top, so no prefix has to preserve a strict decrease. For every weak rule require entrywise \(M_\ell\ge M_r\), \(v_\ell\ge v_r\); for a selected top rule additionally require \((v_\ell)_0\ge(v_r)_0+1\). This is precisely the distinction made by the pinned [driver](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/prover/main.py) and [natural implementation](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/prover/natural.py).

The same conditions with exact nonnegative real entries are sound. A top strict rule drops the first coordinate by at least one for every nonnegative suffix value. Weak steps remain nonincreasing under arbitrary prefixes. The first coordinate stays nonnegative, so there can be only finitely many strict top steps. Rational coefficients should be checked as exact fractions; general algebraic coefficients need exact algebraic comparisons. The existing integer full-rewriting checker does not validate this target.

The authors' top arctic mode permits affine vectors and signed coefficients in \(\mathbb Z\cup\{-\infty\}\). Its carrier is \(\mathbb N\times(\mathbb Z\cup\{-\infty\})^{k-1}\). For every symbol require \((M_s)_{00}\ge0\) **or** \((v_s)_0\ge0\), ensuring that the first coordinate remains a nonnegative integer. Weak rule comparisons include both matrix and vector entries. A strict top comparison requires every corresponding matrix entry and vector entry to be larger, or both to be −∞. Composition is \(M_{uv}=M_u\otimes M_v\), \(v_{uv}=M_u\otimes v_v\oplus v_u\). See the pinned [arctic implementation](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/prover/arctic.py).

## 3. Stages and independent-checker requirements

The simplest stage protocol keeps **all eleven weak rules fixed at every stage**. Each stage validates the inequalities for T, selects a nonempty subset of still-uncovered B-rules, and checks unit strict gaps for those rules. The lifting argument proves each selected subset occurs only finitely often in any full derivation. Once all three B-rules are covered, every B-step occurs only finitely often, and T\B termination closes the proof. Different stages can use different dimensions and interpretations.

It is also sound to delete a rule from later weak obligations after its full relative termination has been established, but that requires the checker to track the full rule-removal chain explicitly. Keeping T fixed is more restrictive and simpler to audit.

A dedicated checker should enforce:

1. Exact canonical T, explicit orientation, and a fixed distinguished set: forward B or reversed D.
2. All seven symbol maps, exact coefficient types, nonnegative entries for natural/rational mode, and valid dimensions. Zero matrices are allowed in this top mode.
3. Leftmost-outermost composition using unbounded integer or exact rational arithmetic; all weak inequalities for the fixed eleven rules at every stage.
4. A unit first-offset gap for each claimed natural/rational strict top rule; nonempty disjoint stage selections covering the distinguished set before reporting completion.
5. The top-to-full lifting theorem and the appropriate elementary residual termination argument as explicit proof obligations. A top certificate for an arbitrary swap rule is not licensed by this reduction.
6. For arctic mode, exact −∞ handling, affine composition, carrier preservation, and every-entry strict comparisons for both matrices and vectors.

A certificate covering only one distinguished rule remains incomplete under this minimal protocol. It can close the problem if accompanied by an independently verified certificate for the corresponding ten-rule residual system, as described next.

## 4. What the published partial certificates prove

Section 4.3 proves termination of all eleven subsystems obtained by deleting one original rule. Each proof omits that rule **before** orienting the remaining ones. Thus proving relative termination of even one original rule against full T would finish the conjecture when combined with its residual proof. This is not a published first removal from full T.

For a concrete independently checked example, [published-subsystem-af-removed.json](published-subsystem-af-removed.json) transcribes the two-dimensional natural matrices of Example 4.3. All ten retained rules are strictly decreasing; the excluded `af -> eb` fails even the weak comparison. This is a complete certificate for exactly T\{af→eb}, not for T.

The repository provides all eleven relative problems and proof logs. For example, [relative/collatz-T-07.srs](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/relative/collatz-T-07.srs) omits `bf -> ga`; its [four-dimensional arctic log](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/proofs/collatz-T-07.log) removes `cg -> cab`, then `cf -> caa`, then `ce -> cb`, all as top rules. It then uses termination of the residual subsystem of T\B. The first stage is not weakly constrained by the omitted `bf -> ga`. The complete list of reproduction settings is in [proofs.sh](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/proofs.sh).

## 5. Exact dependency-pair alternative

The pinned [rules.py](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/prover/rules.py) marks the root of every left side, and produces a marked suffix for every right-side occurrence whose symbol is defined. For forward T the defined symbols are `a,b,c`. Its exact fourteen strict top pairs are:

```text
a# e |-> a#
a# f |-> b#
a# g |-> a#
b# e |-> b#
b# f |-> a#
b# g |-> b#
c# e |-> c# b
c# e |-> b#
c# f |-> c# a a
c# f |-> a# a
c# f |-> a#
c# g |-> c# a b
c# g |-> a# b
c# g |-> b#
```

They are accompanied by all eleven original rules as ordinary weak rules, giving ten symbols total. Standard dependency-pair termination gives SN(T) iff SN(DP(T)_top / T); the [Arts–Giesl author preprint](https://verify.rwth-aachen.de/giesl/papers/TCS-distribute.pdf), Definition 3 and Theorem 6, supplies the underlying theorem. Complete removal of the fourteen pairs with the original weak rules retained would suffice. Partial pair removal leaves an explicit residual obligation; it does not identify an original rule as globally removable without further reasoning. The direct three-rule B target above needs less machinery.

## 6. Tiling: implemented transformation and sufficient chain

The repository's `tile` function uses overlapping adjacent pairs, not an arbitrary geometric tiling. Let \(\tau(s_1\cdots s_m)= (s_1,s_2)\cdots(s_{m-1},s_m)\).

For full rewriting, it generates \(\tau(p\ell q)\to\tau(prq)\) for each rule and all \(p\in\Sigma\cup\{<\}\), \(q\in\Sigma\cup\{>\}\). Every rewrite of a word w is simulated on \(\tau(<w>)\) by one such rule, with unchanged surrounding pair symbols. Therefore termination of the generated tiled system implies termination of the original system. This one-way simulation is sufficient; no claim about arbitrary incompatible tile strings is needed.

For a top problem, use \(\tau(w>)\), without the left sentinel. A strict top rule receives only right padding q and remains top. An ordinary weak rule receives left padding from \(\Sigma\), without `<`, and right padding from \(\Sigma\cup\{>\}\). For the B target, canonical words always begin with `c`; an ordinary non-B rule cannot rewrite that root, and root B-steps have the corresponding top tiled rules. Thus this simulation covers the canonical derivations needed for the lifting proof. The same applies to the reversed-D target and to marked dependency-pair chains. One should not infer a general top-tiling theorem from the implementation without this root check.

For forward T, the implementation generates 704 full tiled rules over 62 symbols. Applying dependency pairs first and then tiling generates 154 strict top rules and 1,210 ordinary weak rules over 102 symbols. A checker would need to regenerate these rules from the pinned transformation and verify the simulation and complete strict-rule coverage; accepting a user-supplied reduced tile list would leave an unproved reachability assumption. The related [Geser–Hofbauer–Waldmann tiling paper](https://doi.org/10.4230/LIPIcs.FSCD.2019.21) develops the broader theory. Tiling is not needed for the direct B-top target.
