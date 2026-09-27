# Exact rewriting formulation and certificate audit

The selected mixed-base system is equivalent to the full positive-integer Collatz conjecture. Its termination has not been proved here. The authoritative reference is Yolcu–Aaronson–Heule, *An Automated Approach to the Collatz Conjecture*, [author PDF](https://emreyolcu.com/research/rewriting-collatz.pdf), [journal DOI](https://doi.org/10.1007/s10817-022-09658-8). The equivalence is Theorem 3.17; Lemma 3.16 supplies the reduction from arbitrary strings to canonical representations.

## Rules and arithmetic meaning

The [authors' rule file](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/rules/collatz-T.srs) contains exactly:

```text
ad -> d
bd -> gd
ae -> ea
af -> eb
ag -> fa
be -> fb
bf -> ga
bg -> gb
ce -> cb
cf -> caa
cg -> cab
```

Call the first two rules D, the next six A, and the last three B; X=A∪B. A canonical word is `c` followed by any string of `a,b,e,f,g`, followed by `d`. Start with value 1 at `c`; reading from left to right, `a,b` apply 2x,2x+1 and `e,f,g` apply 3x,3x+1,3x+2. The terminal `d` leaves the value unchanged. These arithmetic maps must not be confused with the ranking interpretations below.

Here is an independent elementary verification of the equivalence from this ASCII table. Every X-rule preserves value. The D-rules apply the shortcut Collatz map T(n)=n/2 for even n and T(n)=(3n+1)/2 for odd n. The sole canonical word of value 1 is `cd`, which is irreducible.

X terminates: every B-step reduces the number of ternary symbols; once B-steps cease, A-steps reduce the number of pairs consisting of a binary symbol before a ternary symbol. If a canonical word has value greater than 1, it has a digit. If there is a binary digit, A can move the rightmost such digit to the end and enable D. Otherwise B first creates a binary digit. Consequently, every nonconvergent positive T-orbit generates an infinite rewrite sequence. Conversely, an infinite canonical derivation must contain infinitely many D-steps because X terminates; its successive values therefore form a T-orbit that never reaches 1.

To cover arbitrary strings, note that the sequence of boundary symbols `c,d` never changes. Each digit block between consecutive boundaries evolves independently. A block lacking left boundary `c` has no B-steps; its D-steps consume binary digits and hence occur only finitely often, after which A terminates. A block lacking right boundary `d` has no D-steps and terminates under X. The only potentially infinite components are thus canonical `c...d` components. There are finitely many blocks, so termination on canonical components implies termination on every word. This also shows why a proof limited to one chosen rewrite strategy would be insufficient.

## Natural matrix certificates

Use `[s](x)=M_s x+v_s` on N^k, with nonnegative integer matrices and vectors. Word composition is **leftmost outermost**:

```text
[uv] = [u] composed with [v]
M_uv = M_u M_v
v_uv = M_u v_v + v_u.
```

This is the opposite evaluation direction from the arithmetic meaning above. Weak vector comparison is componentwise ≥; strict comparison additionally requires the first component to be greater. Require `(M_s)[0,0] >= 1` for every symbol, ensuring that strict decreases survive arbitrary left contexts. For every weak rule require `M_left >= M_right` and `v_left >= v_right` entrywise. A strict rule additionally requires `v_left[0] > v_right[0]`. These are the exact tests implemented in the authors' [natural encoder/decoder](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/prover/natural.py); composition is explicit in [decoder.py](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/prover/decoder.py).

## Arctic certificates

For full rewriting, the authors use linear matrices over N∪{−∞}, with max as addition and ordinary addition as multiplication; −∞ is absorbing for multiplication. All affine constants are −∞. Each symbol has a finite nonnegative `(0,0)` entry. The carrier is N×(N∪{−∞})^(k−1). Weak matrix comparison is entrywise ≥. A strict rule requires **every** corresponding matrix entry to satisfy x>y or x=y=−∞, not merely one distinguished entry. These sufficient conditions and the absence of finite affine constants in full mode can be checked directly in [arctic.py](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/prover/arctic.py).

Top rewriting permits weaker context conditions and allows the authors' signed arctic coefficients and affine constants. It is a different proof problem. A top/suffix certificate needs a justified reduction to that problem; one cannot silently substitute it for full termination. The [driver](https://github.com/emreyolcu/rewriting-collatz/blob/8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340/prover/main.py) distinguishes these modes and disallows negative arctic coefficients in full mode.

In either semiring, making a subset R strict while keeping the other rules weak proves that R-steps occur only finitely often. To conclude full termination, termination of the remaining system must also be established. For example, making both D-rules strict would suffice because X is already known to terminate. A certificate removing just one rule is a valid intermediate result, not by itself a Collatz proof.

## Scope of the published obstruction

The paper's Theorem 3.8 rules out natural affine matrix rule removal in every dimension for **Zantema's unary system Z**. Theorem 3.10 proves the corresponding obstruction for the stated residual dependency-pair/top problem; reversed unary rules are covered too. These results do not establish impossibility for this mixed-base system, for arctic interpretations, or for arbitrary termination methods. The authors explicitly distinguish the mixed-base representation from the unary obstruction. See Sections 3.1.1–3.2 of the [paper](https://emreyolcu.com/research/rewriting-collatz.pdf).

## Reproducibility and interpretation of search outcomes

The [authors' repository](https://github.com/emreyolcu/rewriting-collatz) was checked at commit `8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340`. The exact raw `rules/collatz-T.srs` bytes have SHA-256 `26c0d7900c4a5a84b568c1b06200760590f8a6b80e221e267da0f30e2b6ce147`.

The driver bounds intermediate arithmetic as well as input entries. An UNSAT result excludes that bounded encoding, not all interpretations in that dimension or even every interpretation with the stated input bound. `-any` seeks removal of at least one rule. `-rev`, `-dp`, and tiling options alter the searched formulation and must be recorded with a result. The authors' decoder uses NumPy `int64`; independent certificate verification should use unbounded integers and explicit −∞ handling. These observations come from the pinned implementation, not from an assumption that a SAT solver's status proves the original mathematical problem.
