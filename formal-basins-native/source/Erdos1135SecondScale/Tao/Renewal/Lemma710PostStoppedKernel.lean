/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma710KernelWindow
import Erdos1135SecondScale.Tao.Renewal.PathGrowth
import Erdos1135SecondScale.Tao.Renewal.Prop78Case3Stopping
import Erdos1135SecondScale.Tao.Renewal.VerticalFirstPassageBasic

/-!
# Lemma 7.10 Post-Stopped Source Ledger

This module starts the source-facing layer below the generic post-stopped
kernel socket.  It names Tao Lemma 7.10's vertical first-passage prefix and a
support-only random-`k` ledger that can later feed
`OneCenterPostStoppedKernelInput`.

It does not prove the first-passage law `(7.48)`, event coverage, residual
mass control, stopped independence, near-window comparison, Lemma 7.10,
Lemma 7.9, Proposition 7.8, or Tao's theorem.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Lemma710

/--
After a checked prefix, continuing along an appended tail agrees with starting
from the prefix endpoint and running along the tail.  This is the deterministic
path identity needed before post-`k` tail events are connected to the source
first-passage prefix.
-/
theorem renewalPathPoint_append_prefix_add
    (start : TaoSection7RenewalPoint) :
    ∀ (pre tail : List TaoSection7RenewalPoint) (p : ℕ),
      taoSection7RenewalPathPoint start (pre ++ tail) (pre.length + p) =
        taoSection7RenewalPathPoint
          (taoSection7RenewalPathPoint start pre pre.length) tail p
  | [], tail, p => by simp
  | h :: pre, tail, p => by
      simpa [taoSection7RenewalPathPoint, Nat.succ_add] using
        renewalPathPoint_append_prefix_add (start + h) pre tail p

/--
Taking a long enough prefix of a finite renewal path does not change any path
point before the prefix cutoff.
-/
theorem renewalPathPoint_take_eq_of_le
    (start : TaoSection7RenewalPoint) :
    ∀ (holds : List TaoSection7RenewalPoint) (n m : ℕ),
      n ≤ m →
        taoSection7RenewalPathPoint start (holds.take m) n =
          taoSection7RenewalPathPoint start holds n
  | holds, 0, m, _hm => by simp
  | [], n + 1, m, _hm => by simp
  | h :: hs, n + 1, 0, hm => by omega
  | h :: hs, n + 1, m + 1, hm => by
      have hn : n ≤ m := Nat.succ_le_succ_iff.mp hm
      simpa [taoSection7RenewalPathPoint] using
        renewalPathPoint_take_eq_of_le (start + h) hs n m hn

/--
Finite least-crossing extraction for Tao Lemma 7.10's vertical first-passage
prefix.

If a finite Hold path has some positive time at or before its length where the
vertical coordinate rises past `start.l + s`, then the least such time gives a
`VerticalFirstPassagePrefix` for the corresponding `take K` prefix.
-/
theorem exists_verticalFirstPassagePrefix_of_exists_crossing
    {start : TaoSection7RenewalPoint} {s : ℕ}
    {holds : List TaoSection7RenewalPoint}
    (hcross :
      ∃ K : ℕ,
        0 < K ∧ K ≤ holds.length ∧
          start.l + (s : ℤ) <
            (taoSection7RenewalPathPoint start holds K).l) :
    ∃ K : ℕ, ∃ pre : List TaoSection7RenewalPoint,
      K ≤ holds.length ∧ pre = holds.take K ∧
        VerticalFirstPassagePrefix start s K pre := by
  classical
  let P : ℕ → Prop := fun K =>
    0 < K ∧ K ≤ holds.length ∧
      start.l + (s : ℤ) <
        (taoSection7RenewalPathPoint start holds K).l
  let K := Nat.find (p := P) hcross
  have hK : P K := Nat.find_spec (p := P) hcross
  refine ⟨K, holds.take K, hK.2.1, rfl, ?_⟩
  refine
    { K_pos := hK.1
      length_eq := ?_
      crosses := ?_
      minimal := ?_ }
  · simp [List.length_take, hK.2.1]
  · have htake :
        taoSection7RenewalPathPoint start (holds.take K) K =
          taoSection7RenewalPathPoint start holds K :=
      renewalPathPoint_take_eq_of_le start holds K K le_rfl
    simpa [htake] using hK.2.2
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hklen : k ≤ holds.length := (Nat.le_of_lt hk).trans hK.2.1
      have htake :
          taoSection7RenewalPathPoint start (holds.take K) k =
            taoSection7RenewalPathPoint start holds k :=
        renewalPathPoint_take_eq_of_le start holds k K (Nat.le_of_lt hk)
      by_contra hnot_le
      have hcross_k :
          start.l + (s : ℤ) <
            (taoSection7RenewalPathPoint start holds k).l := by
        have hlt :
            start.l + (s : ℤ) <
              (taoSection7RenewalPathPoint start (holds.take K) k).l :=
          lt_of_not_ge hnot_le
        simpa [htake] using hlt
      have hnotP : ¬ P k := Nat.find_min (p := P) hcross hk
      exact hnotP ⟨hkpos, hklen, hcross_k⟩

/--
Source-suffix specialization of
`exists_verticalFirstPassagePrefix_of_exists_crossing`.

The length side condition is stated in terms of the source suffix list, while
the selected prefix is the corresponding `take K` of the mapped Hold
increments.
-/
theorem exists_verticalFirstPassagePrefix_of_sourceSuffixes_crossing
    {start : TaoSection7RenewalPoint} {s : ℕ}
    {sourceSuffixes : List (List ℕ)}
    (hcross :
      ∃ K : ℕ,
        0 < K ∧ K ≤ sourceSuffixes.length ∧
          start.l + (s : ℤ) <
            (taoSection7RenewalPathPoint start
              (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) K).l) :
    ∃ K : ℕ, ∃ pre : List TaoSection7RenewalPoint,
      K ≤ sourceSuffixes.length ∧
        pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K ∧
          VerticalFirstPassagePrefix start s K pre := by
  have hcross' :
      ∃ K : ℕ,
        0 < K ∧
          K ≤ (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).length ∧
            start.l + (s : ℤ) <
              (taoSection7RenewalPathPoint start
                (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) K).l := by
    rcases hcross with ⟨K, hKpos, hKlen, hKcross⟩
    refine ⟨K, hKpos, ?_, hKcross⟩
    simpa [taoSection7HoldIncrementsOfPrefixes] using hKlen
  rcases exists_verticalFirstPassagePrefix_of_exists_crossing
      (start := start) (s := s)
      (holds := taoSection7HoldIncrementsOfPrefixes sourceSuffixes) hcross' with
    ⟨K, pre, hKlen, hpre, hfirst⟩
  refine ⟨K, pre, ?_, hpre, hfirst⟩
  simpa [taoSection7HoldIncrementsOfPrefixes] using hKlen

/--
Horizon-aware source-suffix first-passage extraction.

When the supplied crossing is specifically at horizon `N`, the least crossing
time is recorded as `K <= N`.  This is the arithmetic needed to rewrite the
fixed event horizon as `K + (N - K)`.
-/
theorem exists_verticalFirstPassagePrefix_le_of_sourceSuffixes_crossing
    {start : TaoSection7RenewalPoint} {s N : ℕ}
    {sourceSuffixes : List (List ℕ)}
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hcross :
      start.l + (s : ℤ) <
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l) :
    ∃ K : ℕ, ∃ pre : List TaoSection7RenewalPoint,
      K ≤ N ∧ K ≤ sourceSuffixes.length ∧
        pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K ∧
          VerticalFirstPassagePrefix start s K pre := by
  classical
  let holds := taoSection7HoldIncrementsOfPrefixes sourceSuffixes
  let P : ℕ → Prop := fun K =>
    0 < K ∧ K ≤ sourceSuffixes.length ∧
      start.l + (s : ℤ) <
        (taoSection7RenewalPathPoint start holds K).l
  have hcross_exists : ∃ K : ℕ, P K := ⟨N, hNpos, hNle, hcross⟩
  let K := Nat.find (p := P) hcross_exists
  have hK : P K := Nat.find_spec (p := P) hcross_exists
  have hKleN : K ≤ N :=
    Nat.find_min' (p := P) hcross_exists ⟨hNpos, hNle, hcross⟩
  refine ⟨K, holds.take K, hKleN, hK.2.1, rfl, ?_⟩
  refine
    { K_pos := hK.1
      length_eq := ?_
      crosses := ?_
      minimal := ?_ }
  · dsimp [holds]
    simp [List.length_take, taoSection7HoldIncrementsOfPrefixes, hK.2.1]
  · have htake :
        taoSection7RenewalPathPoint start (holds.take K) K =
          taoSection7RenewalPathPoint start holds K :=
      renewalPathPoint_take_eq_of_le start holds K K le_rfl
    simpa [holds, htake] using hK.2.2
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hklen : k ≤ sourceSuffixes.length :=
        (Nat.le_of_lt hk).trans hK.2.1
      have htake :
          taoSection7RenewalPathPoint start (holds.take K) k =
            taoSection7RenewalPathPoint start holds k :=
        renewalPathPoint_take_eq_of_le start holds k K (Nat.le_of_lt hk)
      by_contra hnot_le
      have hcross_k :
          start.l + (s : ℤ) <
            (taoSection7RenewalPathPoint start holds k).l := by
        have hlt :
            start.l + (s : ℤ) <
              (taoSection7RenewalPathPoint start (holds.take K) k).l :=
          lt_of_not_ge hnot_le
        simpa [htake] using hlt
      have hnotP : ¬ P k := Nat.find_min (p := P) hcross_exists hk
      exact hnotP ⟨hkpos, hklen, hcross_k⟩

/--
Support-only source ledger for Tao Lemma 7.10's random vertical first-passage
time `k`.

The fields tie a finite stopped prefix item `(K, holdPrefix)` to the source
suffix beginning at q-relative time `first - q`, record a source start point
and a Hold-prefix/source-prefix bridge, and carry the vertical first-passage
certificate.  This record is not probability credit: direct event coverage or
residual mass control is intentionally kept in the separate
`RandomKSourceLedgerWithMassAccounting` wrapper below.
-/
structure RandomKSourceLedger
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle)
    (q first K verticalGap : ℕ)
    (start : TaoSection7RenewalPoint)
    (holdPrefix : List TaoSection7RenewalPoint) : Prop where
  q_lt_first : q < first
  K_eq_first_sub_q : K = first - q
  K_le_source_length : K ≤ sourceSuffixes.length
  start_eq_source :
    start = taoSection7SourceHitPoint j sourceHeight firstBlock
  point_q_eq :
    pointAt q = start.toPoint
  verticalGap_eq :
    old.cornerL - (pointAt q).l = (verticalGap : ℤ)
  holdPrefix_eq_source :
    holdPrefix =
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K
  first_point_eq :
    pointAt first =
      (taoSection7RenewalPathPoint start holdPrefix K).toPoint
  vertical_first :
    VerticalFirstPassagePrefix start verticalGap K holdPrefix
  prefix_ok :
    PrefixOK (K, holdPrefix)

theorem randomKSourceLedger_prefix_ok
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle}
    {q first K verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {holdPrefix : List TaoSection7RenewalPoint}
    (h :
      RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
        sourceSuffixes old q first K verticalGap start holdPrefix) :
    PrefixOK (K, holdPrefix) :=
  h.prefix_ok

theorem randomKSourceLedger_holdPrefix_length_eq
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle}
    {q first K verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {holdPrefix : List TaoSection7RenewalPoint}
    (h :
      RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
        sourceSuffixes old q first K verticalGap start holdPrefix) :
    holdPrefix.length = K :=
  h.vertical_first.length_eq

theorem randomKSourceLedger_q_add_K_eq_first
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle}
    {q first K verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {holdPrefix : List TaoSection7RenewalPoint}
    (h :
      RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
        sourceSuffixes old q first K verticalGap start holdPrefix) :
    q + K = first := by
  calc
    q + K = q + (first - q) := by rw [h.K_eq_first_sub_q]
    _ = first := Nat.add_sub_of_le (Nat.le_of_lt h.q_lt_first)

/--
Construct a random-`k` source ledger from a finite source-suffix crossing.

The theorem extracts the least vertical first-passage prefix from the supplied
crossing, then packages the remaining source/path compatibility fields into a
`RandomKSourceLedger`.  It does not select the item into a finite family `S`;
that remains the event-to-item producer's job.
-/
theorem exists_randomKSourceLedger_of_sourceSuffixes_crossing
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hcross :
      ∃ K : ℕ,
        0 < K ∧ K ≤ sourceSuffixes.length ∧
          start.l + (verticalGap : ℤ) <
            (taoSection7RenewalPathPoint start
              (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) K).l)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre)) :
    ∃ item : ℕ × List TaoSection7RenewalPoint,
      ∃ first : ℕ,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 := by
  rcases exists_verticalFirstPassagePrefix_of_sourceSuffixes_crossing
      (start := start) (s := verticalGap)
      (sourceSuffixes := sourceSuffixes) hcross with
    ⟨K, pre, hKlen, hpre, hfirst⟩
  refine ⟨(K, pre), q + K, ?_⟩
  exact
    { q_lt_first := by
        have hKpos : 0 < K := hfirst.K_pos
        omega
      K_eq_first_sub_q := by omega
      K_le_source_length := hKlen
      start_eq_source := hstart
      point_q_eq := hpoint_q
      verticalGap_eq := hverticalGap
      holdPrefix_eq_source := hpre
      first_point_eq := hpoint_first K pre hKlen hpre
      vertical_first := hfirst
      prefix_ok := hprefix_ok K pre hKlen hpre hfirst }

/--
Horizon-aware version of
`exists_randomKSourceLedger_of_sourceSuffixes_crossing`.

It remembers that the extracted first-passage time `K` is at most the supplied
fixed horizon `N`, so later code can use `N - K` as the post-`k` tail length.
-/
theorem exists_randomKSourceLedger_of_sourceSuffixes_crossing_at
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap N : ℕ}
    {start : TaoSection7RenewalPoint}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hcross :
      start.l + (verticalGap : ℤ) <
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre)) :
    ∃ item : ℕ × List TaoSection7RenewalPoint,
      ∃ first : ℕ,
        item.1 ≤ N ∧
          RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
            sourceSuffixes old q first item.1 verticalGap start item.2 := by
  rcases exists_verticalFirstPassagePrefix_le_of_sourceSuffixes_crossing
      (start := start) (s := verticalGap)
      (sourceSuffixes := sourceSuffixes) hNpos hNle hcross with
    ⟨K, pre, hKleN, hKlen, hpre, hfirst⟩
  refine ⟨(K, pre), q + K, hKleN, ?_⟩
  exact
    { q_lt_first := by
        have hKpos : 0 < K := hfirst.K_pos
        omega
      K_eq_first_sub_q := by omega
      K_le_source_length := hKlen
      start_eq_source := hstart
      point_q_eq := hpoint_q
      verticalGap_eq := hverticalGap
      holdPrefix_eq_source := hpre
      first_point_eq := hpoint_first K pre hKlen hpre
      vertical_first := hfirst
      prefix_ok := hprefix_ok K pre hKlen hpre hfirst }

/--
For a single random-`k` source ledger, identifying a full source-side Hold list
with the ledger's source suffixes gives the deterministic append split after
the certified stopped prefix.

This supplies only the `full = pre ++ tail` and `tail.length = p` pieces of a
future selected source split.  It does not select an item from a finite family
and does not prove any prefix headroom or probability estimate.
-/
theorem randomKSourceLedger_append_split_of_full_source
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle}
    {q first K verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {holdPrefix full : List TaoSection7RenewalPoint}
    {p : ℕ}
    (h :
      RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
        sourceSuffixes old q first K verticalGap start holdPrefix)
    (hfull : full = taoSection7HoldIncrementsOfPrefixes sourceSuffixes)
    (hp : p = sourceSuffixes.length - K) :
    ∃ tail : List TaoSection7RenewalPoint,
      full = holdPrefix ++ tail ∧ tail.length = p := by
  let fullSource := taoSection7HoldIncrementsOfPrefixes sourceSuffixes
  refine ⟨fullSource.drop K, ?_, ?_⟩
  · rw [hfull, h.holdPrefix_eq_source]
    exact (List.take_append_drop K fullSource).symm
  · rw [hp]
    dsimp [fullSource]
    simp [taoSection7HoldIncrementsOfPrefixes]

/--
Truncated-horizon version of
`randomKSourceLedger_append_split_of_full_source`.

Use this when `sourceSuffixes` is a longer remaining source list and `full`
is only the fixed `K+p` horizon relevant to Tao's Lemma 7.10 event.
-/
theorem randomKSourceLedger_append_split_of_source_take_horizon
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle}
    {q first K verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {holdPrefix full : List TaoSection7RenewalPoint}
    {p : ℕ}
    (h :
      RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
        sourceSuffixes old q first K verticalGap start holdPrefix)
    (horizon : K + p ≤ sourceSuffixes.length)
    (hfull : full =
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take (K + p)) :
    ∃ tail : List TaoSection7RenewalPoint,
      full = holdPrefix ++ tail ∧ tail.length = p := by
  let fullSource := taoSection7HoldIncrementsOfPrefixes sourceSuffixes
  refine ⟨(fullSource.drop K).take p, ?_, ?_⟩
  · rw [hfull, h.holdPrefix_eq_source]
    dsimp [fullSource]
    exact List.take_add
  · dsimp [fullSource]
    have hlen :
        p ≤
          (List.drop K
            (taoSection7HoldIncrementsOfPrefixes sourceSuffixes)).length := by
      rw [List.length_drop]
      have hlenSource :
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).length =
            sourceSuffixes.length := by
        simp [taoSection7HoldIncrementsOfPrefixes]
      rw [hlenSource]
      have horizon' : p + K ≤ sourceSuffixes.length := by
        simpa [Nat.add_comm] using horizon
      omega
    exact List.length_take_of_le hlen

/--
If the same source-event list is both the fixed event horizon `Nevent` and the
source cut at `first - q + p`, then the event horizon is `K+p` for the
ledger's certified first-passage time `K`.

This is the deterministic source-cut equality needed before the fixed-`p`
candidate constructor; it does not prove that Tao's source event has this cut.
-/
theorem randomKSourceLedger_fixedHorizonEq_of_full_first_add_p
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle}
    {q first K p Nevent verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {full holdPrefix : List TaoSection7RenewalPoint}
    (hledger :
      RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
        sourceSuffixes old q first K verticalGap start holdPrefix)
    (hfullN :
      full =
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take Nevent)
    (hNle : Nevent ≤ sourceSuffixes.length)
    (hfullFirstP :
      full =
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (first - q + p))
    (hfirstP_le : first - q + p ≤ sourceSuffixes.length) :
    Nevent = K + p := by
  let holds := taoSection7HoldIncrementsOfPrefixes sourceSuffixes
  have hholds_len : holds.length = sourceSuffixes.length := by
    simp [holds, taoSection7HoldIncrementsOfPrefixes]
  have hlenN : full.length = Nevent := by
    rw [hfullN]
    simp [holds, List.length_take, hholds_len, hNle]
  have hlenFirstP : full.length = first - q + p := by
    rw [hfullFirstP]
    simp [holds, List.length_take, hholds_len, hfirstP_le]
  have hN_firstP : Nevent = first - q + p := hlenN.symm.trans hlenFirstP
  calc
    Nevent = first - q + p := hN_firstP
    _ = K + p := by rw [← hledger.K_eq_first_sub_q]

/--
Mass-accounted wrapper for the random-`k` source ledger.

Future Lemma 7.10 probability work should consume this stronger surface, not
the support-only ledger, when claiming that the finite prefix family accounts
for the relevant source event.  The two accounting propositions are explicit
parameters so a later theorem must name the direct coverage or residual bound
it is using.
-/
structure RandomKSourceLedgerWithMassAccounting
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (DirectEventMassAccounted ResidualMassControlled : Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle)
    (q first K verticalGap : ℕ)
    (start : TaoSection7RenewalPoint)
    (holdPrefix : List TaoSection7RenewalPoint) : Prop where
  ledger :
    RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q first K verticalGap start holdPrefix
  mass_accounting :
    DirectEventMassAccounted ∨ ResidualMassControlled

theorem randomKSourceLedgerWithMassAccounting_prefix_ok
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {DirectEventMassAccounted ResidualMassControlled : Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle}
    {q first K verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {holdPrefix : List TaoSection7RenewalPoint}
    (h :
      RandomKSourceLedgerWithMassAccounting PrefixOK
        DirectEventMassAccounted ResidualMassControlled pointAt j
        sourceHeight firstBlock sourceSuffixes old q first K verticalGap start
        holdPrefix) :
    PrefixOK (K, holdPrefix) :=
  h.ledger.prefix_ok

/--
Finite family of random-`k` source ledgers.

This is the source-facing producer shape for the stopped-prefix family consumed
by `OneCenterPostStoppedKernelInput`.  It derives `PrefixOK` and prefix
lengths from per-item vertical first-passage ledgers, while the total prefix
mass bound remains an explicit field.
-/
structure RandomKSourceLedgerFamily
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  ledger :
    ∀ item, item ∈ S →
      ∃ (pointAt : ℕ → TaoSection7Point)
        (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
        (sourceSuffixes : List (List ℕ))
        (old : TaoSection7Triangle)
        (q first verticalGap : ℕ) (start : TaoSection7RenewalPoint),
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2
  mass_le_one :
    (∑ item ∈ S, (taoSection7HoldListPMF item.1 item.2).toReal) ≤ 1

/--
Finite random-`k` source ledger family with the source data fixed across all
selected prefixes.

This prevents the later selected-split producer from hiding compatibility of
`start`, `old`, `q`, and the source suffixes inside the existential fields of
`RandomKSourceLedgerFamily`.
-/
structure RandomKFixedSourceLedgerFamily
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap : ℕ)
    (start : TaoSection7RenewalPoint)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  ledger :
    ∀ item, item ∈ S →
      ∃ first : ℕ,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2
  mass_le_one :
    (∑ item ∈ S, (taoSection7HoldListPMF item.1 item.2).toReal) ≤ 1

/--
Concrete finite family of source-suffix vertical first-passage prefixes.

For fixed source suffix data this is the finite `S` of all prefixes obtained
from `K ≤ sourceSuffixes.length` that satisfy the vertical first-passage
predicate.  It is larger than a singleton and small enough to give a checked
membership target for extracted random-`k` ledgers.
-/
noncomputable def randomKVerticalFirstPassagePrefixFinset
    (start : TaoSection7RenewalPoint) (verticalGap : ℕ)
    (sourceSuffixes : List (List ℕ)) :
    Finset (ℕ × List TaoSection7RenewalPoint) := by
  classical
  exact
    ((Finset.range (sourceSuffixes.length + 1)).filter fun K =>
      VerticalFirstPassagePrefix start verticalGap K
        ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K)).image
      fun K =>
        (K, (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K)

/-- A source first-passage prefix belongs to the concrete finite prefix family. -/
theorem mem_randomKVerticalFirstPassagePrefixFinset
    {start : TaoSection7RenewalPoint} {verticalGap K : ℕ}
    {sourceSuffixes : List (List ℕ)}
    {pre : List TaoSection7RenewalPoint}
    (hK : K ≤ sourceSuffixes.length)
    (hpre :
      pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K)
    (hfirst : VerticalFirstPassagePrefix start verticalGap K pre) :
    (K, pre) ∈
      randomKVerticalFirstPassagePrefixFinset start verticalGap
        sourceSuffixes := by
  classical
  have hfirst_source :
      VerticalFirstPassagePrefix start verticalGap K
        ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K) := by
    simpa [hpre] using hfirst
  rw [randomKVerticalFirstPassagePrefixFinset]
  refine Finset.mem_image.mpr ⟨K, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨?_, hfirst_source⟩
    exact Finset.mem_range.mpr (by omega)
  · simp [hpre]

/--
Every checked random-`k` source ledger lands in the concrete finite
first-passage prefix family for its source suffix list.
-/
theorem randomKSourceLedger_mem_verticalFirstPassagePrefixFinset
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q first K verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {holdPrefix : List TaoSection7RenewalPoint}
    (hledger :
      RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
        sourceSuffixes old q first K verticalGap start holdPrefix) :
    (K, holdPrefix) ∈
      randomKVerticalFirstPassagePrefixFinset start verticalGap
        sourceSuffixes :=
  mem_randomKVerticalFirstPassagePrefixFinset
    hledger.K_le_source_length hledger.holdPrefix_eq_source
    hledger.vertical_first

/--
The concrete vertical first-passage prefix family carries fixed-source ledgers
when supplied with the same source/path compatibility data used by the local
ledger constructor.

The aggregate PMF mass of this non-singleton family is still an explicit
source/probability input.
-/
theorem randomKFixedSourceLedgerFamily_verticalFirstPassagePrefixFinset
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hmass :
      (∑ item ∈
        randomKVerticalFirstPassagePrefixFinset start verticalGap sourceSuffixes,
        (taoSection7HoldListPMF item.1 item.2).toReal) ≤ 1) :
    RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start
      (randomKVerticalFirstPassagePrefixFinset start verticalGap
        sourceSuffixes) where
  ledger := by
    classical
    intro item hitem
    rw [randomKVerticalFirstPassagePrefixFinset] at hitem
    rcases Finset.mem_image.mp hitem with ⟨K, hKmem, hitem_eq⟩
    rcases Finset.mem_filter.mp hKmem with ⟨hKrange, hfirst⟩
    have hKlen : K ≤ sourceSuffixes.length := by
      have hlt : K < sourceSuffixes.length + 1 :=
        Finset.mem_range.mp hKrange
      omega
    symm at hitem_eq
    subst item
    refine ⟨q + K, ?_⟩
    exact
      { q_lt_first := by
          have hKpos : 0 < K := hfirst.K_pos
          omega
        K_eq_first_sub_q := by omega
        K_le_source_length := hKlen
        start_eq_source := hstart
        point_q_eq := hpoint_q
        verticalGap_eq := hverticalGap
        holdPrefix_eq_source := rfl
        first_point_eq := hpoint_first K _ hKlen rfl
        vertical_first := hfirst
        prefix_ok := hprefix_ok K _ hKlen rfl hfirst }
  mass_le_one := hmass

/-- A single Hold-list PMF point mass is at most one. -/
theorem taoSection7HoldListPMF_toReal_le_one
    (K : ℕ) (pre : List TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF K pre).toReal ≤ (1 : ℝ) := by
  have hp_le_one : taoSection7HoldListPMF K pre ≤ (1 : ENNReal) := by
    calc
      taoSection7HoldListPMF K pre ≤
          ∑' x, taoSection7HoldListPMF K x :=
        ENNReal.le_tsum pre
      _ = 1 := PMF.tsum_coe (taoSection7HoldListPMF K)
  exact
    (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (taoSection7HoldListPMF K) pre)
      ENNReal.one_ne_top).mpr hp_le_one

/-- The total selected-prefix mass of a singleton item family is at most one. -/
theorem taoSection7HoldListPMF_singleton_sum_le_one
    (item : ℕ × List TaoSection7RenewalPoint) :
    (∑ x ∈ ({item} : Finset (ℕ × List TaoSection7RenewalPoint)),
      (taoSection7HoldListPMF x.1 x.2).toReal) ≤ (1 : ℝ) := by
  simpa using taoSection7HoldListPMF_toReal_le_one item.1 item.2

/--
Package one checked random-`k` source ledger as a fixed-source singleton family.

This removes the aggregate mass premise only for a singleton selected family;
it does not prove event coverage or justify that a global Tao source selector
uses a singleton.
-/
theorem randomKFixedSourceLedgerFamily_singleton
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hledger :
      ∃ first : ℕ,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2) :
    RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start
      ({item} : Finset (ℕ × List TaoSection7RenewalPoint)) where
  ledger := by
    intro item' hitem'
    rw [Finset.mem_singleton] at hitem'
    subst item'
    exact hledger
  mass_le_one := taoSection7HoldListPMF_singleton_sum_le_one item

/--
A fixed-source random-`k` ledger family can feed the older loose ledger-family
surface by forgetting that all ledgers used the same source data.
-/
theorem randomKFixedSourceLedgerFamily_to_randomKSourceLedgerFamily
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start S) :
    RandomKSourceLedgerFamily PrefixOK S where
  ledger := by
    intro item hitem
    rcases h.ledger item hitem with ⟨first, hledger⟩
    exact
      ⟨pointAt, j, sourceHeight, firstBlock, sourceSuffixes, old, q,
        first, verticalGap, start, hledger⟩
  mass_le_one := h.mass_le_one

/--
Random-`k` source ledger families feed the generic stopped-prefix family
socket.  This closes the prefix certificate and length fields; probability
coverage and the aggregate prefix mass remain separate inputs to the family
record.
-/
theorem randomKSourceLedgerFamily_to_stoppedHoldVariablePrefixFamily
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h : RandomKSourceLedgerFamily PrefixOK S) :
    TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S where
  prefix_ok := by
    intro item hitem
    rcases h.ledger item hitem with
      ⟨pointAt, j, sourceHeight, firstBlock, sourceSuffixes,
        old, q, first, verticalGap, start, hledger⟩
    exact hledger.prefix_ok
  length_eq := by
    intro item hitem
    rcases h.ledger item hitem with
      ⟨pointAt, j, sourceHeight, firstBlock, sourceSuffixes,
        old, q, first, verticalGap, start, hledger⟩
    exact hledger.vertical_first.length_eq
  mass_le_one := h.mass_le_one

/--
Concrete source-event coverage surface for a finite random-`k` ledger family.

The `SourceEvent` predicate is on full source-side Hold-increment lists.
The coverage field says that every source event is either in a named residual
bad set or decomposes as a selected stopped prefix followed by a tail satisfying
the tail event.  This is still support-only: later work must prove this field
and then combine it with a stopped-tail estimate.
-/
structure RandomKSourcePrefixFamilyCoverage
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (SourceEvent ResidualBad : List TaoSection7RenewalPoint → Prop)
    (TailBad :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  prefixes : RandomKSourceLedgerFamily PrefixOK S
  event_cover_or_residual :
    ∀ full, SourceEvent full →
      ResidualBad full ∨
        ∃ item, item ∈ S ∧
          ∃ tail : List TaoSection7RenewalPoint,
            full = item.2 ++ tail ∧ TailBad item.2 tail

theorem randomKSourcePrefixFamilyCoverage_to_stoppedHoldVariablePrefixFamily
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {SourceEvent ResidualBad : List TaoSection7RenewalPoint → Prop}
    {TailBad :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      RandomKSourcePrefixFamilyCoverage PrefixOK SourceEvent ResidualBad
        TailBad S) :
    TaoSection7StoppedHoldVariablePrefixFamily PrefixOK S :=
  randomKSourceLedgerFamily_to_stoppedHoldVariablePrefixFamily h.prefixes

theorem randomKSourcePrefixFamilyCoverage_event_cover_or_residual
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {SourceEvent ResidualBad : List TaoSection7RenewalPoint → Prop}
    {TailBad :
      List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      RandomKSourcePrefixFamilyCoverage PrefixOK SourceEvent ResidualBad
        TailBad S)
    {full : List TaoSection7RenewalPoint}
    (hfull : SourceEvent full) :
    ResidualBad full ∨
      ∃ item, item ∈ S ∧
        ∃ tail : List TaoSection7RenewalPoint,
          full = item.2 ++ tail ∧ TailBad item.2 tail :=
  h.event_cover_or_residual full hfull

/--
Deterministic source-cylinder cover for one-center events from random-`k`
source-prefix coverage.

This discharges the cover input of the one-center source-cylinder
mass-control socket from a supplied random-`k` coverage record for each center.
It still assumes the finite sample event maps into the source event and avoids
the residual event; it is not the probability/source-law mass-control step.
-/
theorem oneCenterSourceCylinderCover_of_randomKSourcePrefixFamilyCoverage
    {Ω : Type*}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {C : Finset TaoSection7Point}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {event : TaoSection7Point → Set Ω}
    {SourceEvent ResidualBad :
      TaoSection7Point → List TaoSection7RenewalPoint → Prop}
    {EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    (hcoverage :
      ∀ c ∈ C,
        RandomKSourcePrefixFamilyCoverage PrefixOK (SourceEvent c)
          (ResidualBad c) (EndpointNearCenter c) S)
    (hsource :
      ∀ c ∈ C, ∀ ω, ω ∈ event c → SourceEvent c (fullOf ω))
    (hnot_residual :
      ∀ c ∈ C, ∀ ω, ω ∈ event c → ¬ ResidualBad c (fullOf ω)) :
    ∀ c ∈ C, ∀ ω, ω ∈ event c →
      ∃ item, item ∈ S ∧
        ∃ tail : List TaoSection7RenewalPoint,
          fullOf ω = item.2 ++ tail ∧
            EndpointNearCenter c item.2 tail := by
  intro c hc ω hω
  rcases
      (hcoverage c hc).event_cover_or_residual (fullOf ω)
        (hsource c hc ω hω) with hres | hhit
  · exact False.elim ((hnot_residual c hc ω hω) hres)
  · exact hhit

/--
One-center event-identification bridge from source-cylinder mass control and
random-`k` source-prefix coverage.

This produces the exact `hidentify` premise for the stopped-tail one-center
wrapper after the source-law mass-control record is supplied.  The theorem
only removes the deterministic cover premise; it does not prove that mass
control or Tao's `(7.48)` kernel estimate.
-/
theorem oneCenterEventIdentification_of_randomKSourcePrefixFamilyCoverage
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω} {p : ℕ}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {C : Finset TaoSection7Point}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {fullOf : Ω → List TaoSection7RenewalPoint}
    {event : TaoSection7Point → Set Ω}
    {SourceEvent ResidualBad :
      TaoSection7Point → List TaoSection7RenewalPoint → Prop}
    {EndpointNearCenter :
      TaoSection7Point →
        List TaoSection7RenewalPoint → List TaoSection7RenewalPoint → Prop}
    [∀ c, DecidableRel (EndpointNearCenter c)]
    (hmass :
      Lemma710OneCenterSourceCylinderMassControl μ p S fullOf event
        EndpointNearCenter)
    (hcoverage :
      ∀ c ∈ C,
        RandomKSourcePrefixFamilyCoverage PrefixOK (SourceEvent c)
          (ResidualBad c) (EndpointNearCenter c) S)
    (hsource :
      ∀ c ∈ C, ∀ ω, ω ∈ event c → SourceEvent c (fullOf ω))
    (hnot_residual :
      ∀ c ∈ C, ∀ ω, ω ∈ event c → ¬ ResidualBad c (fullOf ω)) :
    ∀ c ∈ C,
      pmfProb μ (event c) ≤
        postStoppedOneCenterMass p S (EndpointNearCenter c) :=
  oneCenterEventIdentification_of_sourceCylinderMassControl hmass
    (oneCenterSourceCylinderCover_of_randomKSourcePrefixFamilyCoverage
      hcoverage hsource hnot_residual)

/-- Endpoint of the stopped prefix. -/
def lemma710StoppedPrefixEndpoint
    (start : TaoSection7RenewalPoint)
    (pre : List TaoSection7RenewalPoint) : TaoSection7RenewalPoint :=
  taoSection7RenewalPathPoint start pre pre.length

/--
Endpoint after a stopped prefix and a post-`k` tail of length `p`.

The definition keeps the endpoint in the original source coordinates.  The
already checked `renewalPathPoint_append_prefix_add` theorem rewrites this
endpoint to the restarted post-prefix path when needed.
-/
def lemma710PostKTailEndpoint
    (start : TaoSection7RenewalPoint) (p : ℕ)
    (pre tail : List TaoSection7RenewalPoint) : TaoSection7RenewalPoint :=
  taoSection7RenewalPathPoint start (pre ++ tail) (pre.length + p)

theorem lemma710PostKTailEndpoint_eq_tailPath
    (start : TaoSection7RenewalPoint) (p : ℕ)
    (pre tail : List TaoSection7RenewalPoint) :
    lemma710PostKTailEndpoint start p pre tail =
      taoSection7RenewalPathPoint
        (lemma710StoppedPrefixEndpoint start pre) tail p := by
  simp [lemma710PostKTailEndpoint, lemma710StoppedPrefixEndpoint,
    renewalPathPoint_append_prefix_add]

/--
Source-facing one-center endpoint predicate for Lemma 7.10 after a stopped
prefix and a fixed post-`k` horizon.

The `tail.length = p` field is part of the predicate, so the `p = 0` case
remains represented by the empty tail rather than being discarded by a
positivity/nonempty-tail side condition.
-/
def Lemma710PostKEndpointNearCenter
    (start : TaoSection7RenewalPoint) (p : ℕ) (R : ℝ)
    (c : TaoSection7Point)
    (pre tail : List TaoSection7RenewalPoint) : Prop :=
  tail.length = p ∧
    ((lemma710PostKTailEndpoint start p pre tail).toPoint).distSq c ≤ R ^ 2

/--
Source-side endpoint-near-center event at the full fixed horizon.

This is the source-list version of the one-center event before selecting the
random-`k` stopped prefix and splitting off the post-`k` tail.
-/
def Lemma710SourceEndpointNearCenter
    (start : TaoSection7RenewalPoint) (R : ℝ) (c : TaoSection7Point)
    (full : List TaoSection7RenewalPoint) : Prop :=
  ((taoSection7RenewalPathPoint start full full.length).toPoint).distSq c ≤
    R ^ 2

theorem lemma710PostKEndpointNearCenter_tail_length
    {start : TaoSection7RenewalPoint} {p : ℕ} {R : ℝ}
    {c : TaoSection7Point} {pre tail : List TaoSection7RenewalPoint}
    (h : Lemma710PostKEndpointNearCenter start p R c pre tail) :
    tail.length = p :=
  h.1

theorem lemma710PostKEndpointNearCenter_distSq_le
    {start : TaoSection7RenewalPoint} {p : ℕ} {R : ℝ}
    {c : TaoSection7Point} {pre tail : List TaoSection7RenewalPoint}
    (h : Lemma710PostKEndpointNearCenter start p R c pre tail) :
    ((lemma710PostKTailEndpoint start p pre tail).toPoint).distSq c ≤ R ^ 2 :=
  h.2

theorem lemma710SourceEndpointNearCenter_distSq_le
    {start : TaoSection7RenewalPoint} {R : ℝ} {c : TaoSection7Point}
    {full : List TaoSection7RenewalPoint}
    (h : Lemma710SourceEndpointNearCenter start R c full) :
    ((taoSection7RenewalPathPoint start full full.length).toPoint).distSq c ≤
      R ^ 2 :=
  h

/--
Vertical displacement event for a length-`p` tail after restarting at the
stopped prefix endpoint.

This is deterministic tail-only plumbing for the later Lemma 2.2 producer; it
does not prove the tail bound or the random-`K` source distribution.
-/
def Lemma710VerticalTailDisplacementEvent
    (base : TaoSection7RenewalPoint) (p : ℕ) (tailThreshold : ℝ)
    (tail : List TaoSection7RenewalPoint) : Prop :=
  tail.length = p ∧
    tailThreshold ≤
      (((taoSection7RenewalPathPoint base tail p).l - base.l : ℤ) : ℝ)

/--
Horizontal displacement event for a length-`p` tail after restarting at the
stopped prefix endpoint.
-/
def Lemma710HorizontalTailDisplacementEvent
    (base : TaoSection7RenewalPoint) (p : ℕ) (tailThreshold : ℝ)
    (tail : List TaoSection7RenewalPoint) : Prop :=
  tail.length = p ∧
    tailThreshold ≤
      |(((taoSection7RenewalPathPoint base tail p).j : ℕ) : ℝ) -
        (((base.j : ℕ) : ℝ))|

/--
Canonical first-passage split of a full source-side Hold list once the
selected prefix length `K` and post-`k` horizon `p` account for the full
length.

This closes only the deterministic append/tail-length part of the selected
source split.  Membership in the selected prefix family and prefix headroom
remain separate source-run facts.
-/
theorem lemma710_take_drop_decomposition_of_length
    {full : List TaoSection7RenewalPoint} {K p : ℕ}
    (hlen : full.length = K + p) :
    full = full.take K ++ full.drop K ∧ (full.drop K).length = p := by
  constructor
  · exact (List.take_append_drop K full).symm
  · calc
      (full.drop K).length = full.length - K := by simp
      _ = (K + p) - K := by rw [hlen]
      _ = p := Nat.add_sub_cancel_left K p

theorem lemma710_exists_tail_after_take_of_length
    {full : List TaoSection7RenewalPoint} {K p : ℕ}
    (hlen : full.length = K + p) :
    ∃ tail : List TaoSection7RenewalPoint,
      full = full.take K ++ tail ∧ tail.length = p := by
  refine ⟨full.drop K, ?_⟩
  exact lemma710_take_drop_decomposition_of_length hlen

/--
Vertical part of Tao's exceptional event `E'`, stated on a full source-side
Hold-increment list.

The real threshold parameter is intentionally explicit: later source-fidelity
work should instantiate it with the `2 * A^2 * (1 + p)` scale from the paper.
-/
def EprimeVerticalSourceEvent
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (sourceThreshold : ℝ)
    (full : List TaoSection7RenewalPoint) : Prop :=
  sourceThreshold ≤
    (((taoSection7RenewalPathPoint start full full.length).l -
      old.cornerL : ℤ) : ℝ)

/--
The vertical `E'` source event crosses the old vertical level at the fixed
source horizon when the source threshold is positive.
-/
theorem eprimeVerticalSourceEvent_horizon_crosses
    {pointAt : ℕ → TaoSection7Point}
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {q verticalGap N : ℕ} {sourceThreshold : ℝ}
    {sourceSuffixes : List (List ℕ)}
    {full : List TaoSection7RenewalPoint}
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hthreshold_pos : 0 < sourceThreshold)
    (hfull :
      full = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N)
    (hNle : N ≤ sourceSuffixes.length)
    (hsrc : EprimeVerticalSourceEvent start old sourceThreshold full) :
    start.l + (verticalGap : ℤ) <
      (taoSection7RenewalPathPoint start
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l := by
  have hfull_len : full.length = N := by
    rw [hfull]
    simp [taoSection7HoldIncrementsOfPrefixes, List.length_take, hNle]
  have hendpoint :
      taoSection7RenewalPathPoint start full full.length =
        taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N := by
    rw [hfull_len, hfull]
    exact
      renewalPathPoint_take_eq_of_le start
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N N le_rfl
  have hgap :
      old.cornerL - start.l = (verticalGap : ℤ) := by
    simpa [hpoint_q] using hverticalGap
  have hbase : start.l + (verticalGap : ℤ) = old.cornerL := by omega
  have hdiff_pos_real :
      0 <
        (((taoSection7RenewalPathPoint start full full.length).l -
          old.cornerL : ℤ) : ℝ) :=
    lt_of_lt_of_le hthreshold_pos hsrc
  have hdiff_pos_int :
      0 <
        (taoSection7RenewalPathPoint start full full.length).l -
          old.cornerL := by
    exact_mod_cast hdiff_pos_real
  have hold_lt :
      old.cornerL <
        (taoSection7RenewalPathPoint start full full.length).l := by
    omega
  simpa [hbase, hendpoint] using hold_lt

/--
The vertical `E'` source event gives a positive vertical crossing witness when
the source threshold is positive and `full` is the fixed `N`-step source
horizon.

This only supplies the existence of a crossing time for the least-passage
extractor.  It does not select the least crossing item into `S` or prove any
horizontal/headroom estimate.
-/
theorem eprimeVerticalSourceEvent_to_sourceSuffixes_crossing
    {pointAt : ℕ → TaoSection7Point}
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {q verticalGap N : ℕ} {sourceThreshold : ℝ}
    {sourceSuffixes : List (List ℕ)}
    {full : List TaoSection7RenewalPoint}
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hthreshold_pos : 0 < sourceThreshold)
    (hfull :
      full = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N)
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hsrc : EprimeVerticalSourceEvent start old sourceThreshold full) :
    ∃ K : ℕ,
      0 < K ∧ K ≤ sourceSuffixes.length ∧
        start.l + (verticalGap : ℤ) <
          (taoSection7RenewalPathPoint start
            (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) K).l :=
  ⟨N, hNpos, hNle,
    eprimeVerticalSourceEvent_horizon_crosses hpoint_q hverticalGap
      hthreshold_pos hfull hNle hsrc⟩

/--
Local vertical source-event candidate: from a fixed-horizon vertical `E'`
event and the source/path compatibility fields, produce the first-passage
ledger item together with the exact `K + (N-K)` horizon identity.

This still does not select the item into a finite family `S`, prove prefix
headroom, or bound residual mass.
-/
theorem eprimeVerticalSourceEvent_to_sourceLedgerHorizonCandidate
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap N : ℕ}
    {start : TaoSection7RenewalPoint} {sourceThreshold : ℝ}
    {full : List TaoSection7RenewalPoint}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hthreshold_pos : 0 < sourceThreshold)
    (hfull :
      full = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N)
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hsrc : EprimeVerticalSourceEvent start old sourceThreshold full) :
    ∃ item : ℕ × List TaoSection7RenewalPoint,
      ∃ first postLength : ℕ,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 ∧
          full =
            (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
              (item.1 + postLength) ∧
            item.1 + postLength ≤ sourceSuffixes.length := by
  have hcross :
      start.l + (verticalGap : ℤ) <
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l :=
    eprimeVerticalSourceEvent_horizon_crosses hpoint_q hverticalGap
      hthreshold_pos hfull hNle hsrc
  rcases exists_randomKSourceLedger_of_sourceSuffixes_crossing_at
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (start := start)
      hstart hpoint_q hverticalGap hNpos hNle hcross hpoint_first
      hprefix_ok with
    ⟨item, first, hKleN, hledger⟩
  refine ⟨item, first, N - item.1, hledger, ?_, ?_⟩
  · have hsum : item.1 + (N - item.1) = N := Nat.add_sub_of_le hKleN
    simpa [hsum] using hfull
  · have hsum : item.1 + (N - item.1) = N := Nat.add_sub_of_le hKleN
    simpa [hsum] using hNle

/--
Fixed-`p` version of the local vertical source-event candidate.

The horizon-aware candidate naturally produces post-length `N - K`.  This
adapter consumes an explicit source-run premise identifying that post-length
with Tao's fixed `p`, then exposes the exact fixed-`p` horizon required by the
fixed-horizon selector.
-/
theorem eprimeVerticalSourceEvent_to_fixedPSourceLedgerCandidate
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap N p : ℕ}
    {start : TaoSection7RenewalPoint} {sourceThreshold : ℝ}
    {full : List TaoSection7RenewalPoint}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hthreshold_pos : 0 < sourceThreshold)
    (hfull :
      full = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N)
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hpost_eq :
      ∀ (item : ℕ × List TaoSection7RenewalPoint) (first postLength : ℕ),
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        full =
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
            (item.1 + postLength) →
        item.1 + postLength ≤ sourceSuffixes.length →
        postLength = p)
    (hsrc : EprimeVerticalSourceEvent start old sourceThreshold full) :
    ∃ item : ℕ × List TaoSection7RenewalPoint,
      ∃ first : ℕ,
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 ∧
          full =
            (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
              (item.1 + p) ∧
            item.1 + p ≤ sourceSuffixes.length := by
  rcases eprimeVerticalSourceEvent_to_sourceLedgerHorizonCandidate
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (start := start)
      (sourceThreshold := sourceThreshold) (full := full)
      hstart hpoint_q hverticalGap hthreshold_pos hfull hNpos hNle
      hpoint_first hprefix_ok hsrc with
    ⟨item, first, postLength, hledger, hfull_post, hpost_len⟩
  have hpost : postLength = p :=
    hpost_eq item first postLength hledger hfull_post hpost_len
  refine ⟨item, first, hledger, ?_, ?_⟩
  · simpa [hpost] using hfull_post
  · simpa [hpost] using hpost_len

/--
Shared fixed-`p` source-run candidate selected by the random-`k` source
construction.

This packages the data common to the vertical and horizontal `E'` branches:
the checked random-`k` ledger item, the exact `K+p` source horizon, and the
bound keeping that horizon inside the source suffix list.  Membership in the
finite family `S`, prefix headroom, and residual routing remain separate
source-run obligations.
-/
structure EprimeFixedPSourceRunCandidate
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap : ℕ)
    (start : TaoSection7RenewalPoint) (p : ℕ)
    (full : List TaoSection7RenewalPoint)
    (item : ℕ × List TaoSection7RenewalPoint) : Prop where
  ledger :
    ∃ first : ℕ,
      RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
        sourceSuffixes old q first item.1 verticalGap start item.2
  full_eq :
    full =
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (item.1 + p)
  horizon_le : item.1 + p ≤ sourceSuffixes.length

/--
Branch-neutral source-cut data for Tao Lemma 7.10's selected random-`k`
source run.

This records the source-run producer obligation shared by the vertical and
horizontal `E'` branches: select Tao's vertical first-passage ledger once and
prove the source event is cut at `first - q + p`.  It does not prove that a
vertical or horizontal event supplies this data, and it does not contain
prefix headroom or residual-mass information.
-/
structure Lemma710SourceCutCandidateData
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap : ℕ)
    (start : TaoSection7RenewalPoint) (p : ℕ)
    (full : List TaoSection7RenewalPoint)
    (item : ℕ × List TaoSection7RenewalPoint) : Type where
  first : ℕ
  ledger :
    RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q first item.1 verticalGap start item.2
  source_cut :
    full =
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (first - q + p)
  source_cut_le : first - q + p ≤ sourceSuffixes.length

theorem lemma710SourceCutCandidateData_to_fixedPSourceRunCandidate
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start p full item := by
  exact
    { ledger := ⟨hdata.first, hdata.ledger⟩
      full_eq := by
        simpa [hdata.ledger.K_eq_first_sub_q] using hdata.source_cut
      horizon_le := by
        simpa [hdata.ledger.K_eq_first_sub_q] using hdata.source_cut_le }

/--
Clock-normalization adapter from the fixed-`p` q-relative horizon to the
source-cut data shape.

`EprimeFixedPSourceRunCandidate` stores Tao's random `k` as the q-relative
ledger duration `item.1`, so its horizon is `item.1 + p`.  The source-cut
record stores the same cut as `first - q + p`; the ledger field
`K_eq_first_sub_q` is the checked bridge between those notations.  This does
not produce the fixed-`p` candidate from source/sample data.
-/
theorem lemma710SourceCutCandidateData_nonempty_of_fixedPSourceRunCandidate
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (h :
      EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    Nonempty
      (Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) := by
  rcases h.ledger with ⟨first, hledger⟩
  exact
    ⟨{ first := first
       ledger := hledger
       source_cut := by
        simpa [hledger.K_eq_first_sub_q] using h.full_eq
       source_cut_le := by
        simpa [hledger.K_eq_first_sub_q] using h.horizon_le }⟩

/--
Source-cut data from a real vertical crossing and post-`p` room.

The crossing at horizon `N` selects Tao's q-relative random `k = item.1`;
the post-room premise `N + p <= sourceSuffixes.length` then gives the
canonical source cut `take (item.1 + p)`.  This removes the fixed-`p`
candidate/source-cut oracle for this canonical full list, but it does not
produce sample membership, event membership, finite-PMF laws, or residual
mass control.
-/
theorem lemma710SourceCutCandidateData_nonempty_of_sourceSuffixes_crossing_at_postRoom
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap N p : ℕ}
    {start : TaoSection7RenewalPoint}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hcross :
      start.l + (verticalGap : ℤ) <
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l)
    (hpost_room : N + p ≤ sourceSuffixes.length)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre)) :
    ∃ item : ℕ × List TaoSection7RenewalPoint,
      Nonempty
        (Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
          firstBlock sourceSuffixes old q verticalGap start p
          ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
            (item.1 + p))
          item) := by
  rcases exists_randomKSourceLedger_of_sourceSuffixes_crossing_at
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (start := start)
      hstart hpoint_q hverticalGap hNpos hNle hcross hpoint_first
      hprefix_ok with
    ⟨item, first, hKleN, hledger⟩
  have hhorizon : item.1 + p ≤ sourceSuffixes.length := by
    have hle : item.1 + p ≤ N + p := Nat.add_le_add_right hKleN p
    exact hle.trans hpost_room
  refine ⟨item, ⟨?_⟩⟩
  exact
    { first := first
      ledger := hledger
      source_cut := by
        simp [hledger.K_eq_first_sub_q]
      source_cut_le := by
        simpa [hledger.K_eq_first_sub_q] using hhorizon }

theorem lemma710SourceCutCandidateData_full_eq_fixedHorizon
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    full =
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (item.1 + p) :=
  (lemma710SourceCutCandidateData_to_fixedPSourceRunCandidate hdata).full_eq

theorem lemma710SourceCutCandidateData_horizon_le
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    item.1 + p ≤ sourceSuffixes.length :=
  (lemma710SourceCutCandidateData_to_fixedPSourceRunCandidate hdata).horizon_le

theorem lemma710SourceCutCandidateData_full_length_eq
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    full.length = item.1 + p := by
  rw [lemma710SourceCutCandidateData_full_eq_fixedHorizon hdata]
  simp [taoSection7HoldIncrementsOfPrefixes, List.length_take,
    lemma710SourceCutCandidateData_horizon_le hdata]

/--
Two source-cut candidates for the same source data, same post-length `p`, and
same canonical full window select the same random-`k` item.

This is the source-cut coherence bridge to use when a later sample decode
constructs an item separately from the crossing/post-room existential: the
shared `full` identifies `item.1 + p`, and each ledger identifies `item.2` as
the corresponding source take.
-/
theorem lemma710SourceCutCandidateData_item_eq
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item₁ item₂ : ℕ × List TaoSection7RenewalPoint}
    (h₁ :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item₁)
    (h₂ :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item₂) :
    item₁ = item₂ := by
  have hKp : item₁.1 + p = item₂.1 + p := by
    exact
      (lemma710SourceCutCandidateData_full_length_eq h₁).symm.trans
        (lemma710SourceCutCandidateData_full_length_eq h₂)
  have hK : item₁.1 = item₂.1 := Nat.add_right_cancel hKp
  have hpre : item₁.2 = item₂.2 := by
    calc
      item₁.2 =
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take item₁.1 :=
        h₁.ledger.holdPrefix_eq_source
      _ =
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take item₂.1 := by
        rw [hK]
      _ = item₂.2 := h₂.ledger.holdPrefix_eq_source.symm
  exact Prod.ext hK hpre

theorem lemma710SourceCutCandidateData_fullPath_eq_sourcePrefixPath
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    taoSection7RenewalPathPoint start full full.length =
      taoSection7RenewalPathPoint start
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) (item.1 + p) := by
  rw [lemma710SourceCutCandidateData_full_length_eq hdata,
    lemma710SourceCutCandidateData_full_eq_fixedHorizon hdata]
  exact
    renewalPathPoint_take_eq_of_le start
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes)
      (item.1 + p) (item.1 + p) le_rfl

theorem lemma710SourceCutCandidateData_fullEndpoint_toPoint_eq
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    (taoSection7RenewalPathPoint start full full.length).toPoint =
      (taoSection7RenewalPathPoint start
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes)
        (item.1 + p)).toPoint := by
  rw [lemma710SourceCutCandidateData_fullPath_eq_sourcePrefixPath hdata]

theorem lemma710SourceCutCandidateData_q_add_item_eq_first
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    q + item.1 = hdata.first :=
  randomKSourceLedger_q_add_K_eq_first hdata.ledger

theorem lemma710SourceCutCandidateData_q_add_item_add_p_eq_first_add_p
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    q + item.1 + p = hdata.first + p := by
  rw [lemma710SourceCutCandidateData_q_add_item_eq_first hdata]

theorem lemma710SourceCutCandidateData_pointAt_q_add_item_add_p_eq_fullEndpoint
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint) :
    pointAt (q + item.1 + p) =
      (taoSection7RenewalPathPoint start full full.length).toPoint := by
  have hpoint :=
    hpoint_source (item.1 + p) full
      (lemma710SourceCutCandidateData_horizon_le hdata)
      (lemma710SourceCutCandidateData_full_eq_fixedHorizon hdata)
  simpa [Nat.add_assoc, lemma710SourceCutCandidateData_full_length_eq hdata]
    using hpoint

theorem lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint) :
    pointAt (hdata.first + p) =
      (taoSection7RenewalPathPoint start full full.length).toPoint := by
  have hpoint :
      pointAt (q + item.1 + p) =
        (taoSection7RenewalPathPoint start full full.length).toPoint :=
    lemma710SourceCutCandidateData_pointAt_q_add_item_add_p_eq_fullEndpoint
      hdata hpoint_source
  rwa [lemma710SourceCutCandidateData_q_add_item_add_p_eq_first_add_p hdata]
    at hpoint

theorem lemma710SourceCutCandidateData_append_split
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    ∃ tail : List TaoSection7RenewalPoint,
      full = item.2 ++ tail ∧ tail.length = p :=
  randomKSourceLedger_append_split_of_source_take_horizon hdata.ledger
    (lemma710SourceCutCandidateData_horizon_le hdata)
    (lemma710SourceCutCandidateData_full_eq_fixedHorizon hdata)

/--
A source-cut candidate for a full endpoint-near-center event yields the
fixed-horizon one-center tail predicate for the selected prefix.

This is pointwise deterministic plumbing.  It uses the checked source cut to
split `full` as `item.2 ++ tail` with `tail.length = p`, then rewrites the
source endpoint as `lemma710PostKTailEndpoint start p item.2 tail`.
-/
theorem lemma710SourceCutCandidateData_postKEndpointNearCenter
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {R : ℝ} {c : TaoSection7Point}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hnear : Lemma710SourceEndpointNearCenter start R c full)
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    ∃ tail : List TaoSection7RenewalPoint,
      full = item.2 ++ tail ∧
        Lemma710PostKEndpointNearCenter start p R c item.2 tail := by
  rcases lemma710SourceCutCandidateData_append_split hdata with
    ⟨tail, hfull, htail⟩
  refine ⟨tail, hfull, htail, ?_⟩
  have hendpoint :
      (lemma710PostKTailEndpoint start p item.2 tail).toPoint =
        (taoSection7RenewalPathPoint start full full.length).toPoint := by
    simp [lemma710PostKTailEndpoint, hfull, htail]
  simpa [Lemma710SourceEndpointNearCenter, hendpoint] using hnear

/--
Fixed-horizon one-center source coverage from source-cut candidates.

The selector premise remains the hard source-run producer: for every center and
source endpoint-near-center full list it must either return a residual source
failure or a selected source-cut candidate in the fixed distribution-level
support `S`.  This theorem only packages that pointwise selector into the
generic `RandomKSourcePrefixFamilyCoverage` interface.
-/
theorem randomKSourcePrefixFamilyCoverage_of_sourceCutEndpointNearCenter
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {R : ℝ} {C : Finset TaoSection7Point}
    {ResidualBad : TaoSection7Point → List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hprefixes :
      RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start S)
    (hselect :
      ∀ c ∈ C, ∀ full,
        Lemma710SourceEndpointNearCenter start R c full →
          ResidualBad c full ∨
            ∃ item, item ∈ S ∧
              Nonempty
                (Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
                  firstBlock sourceSuffixes old q verticalGap start p full item)) :
    ∀ c ∈ C,
      RandomKSourcePrefixFamilyCoverage PrefixOK
        (Lemma710SourceEndpointNearCenter start R c)
        (ResidualBad c)
        (Lemma710PostKEndpointNearCenter start p R c)
        S := by
  intro c hc
  refine
    { prefixes := randomKFixedSourceLedgerFamily_to_randomKSourceLedgerFamily hprefixes
      event_cover_or_residual := ?_ }
  intro full hnear
  rcases hselect c hc full hnear with hres | hcandidate
  · exact Or.inl hres
  · rcases hcandidate with ⟨item, hitem, hdata⟩
    rcases hdata with ⟨hdata⟩
    rcases lemma710SourceCutCandidateData_postKEndpointNearCenter hnear hdata with
      ⟨tail, hfull, htail⟩
    exact Or.inr ⟨item, hitem, tail, hfull, htail⟩

/--
Source-provenance input for the one-center `hselect` gate.

This is stronger than endpoint geometry alone: it records the full-window
source path, the selected random-`k` ledger, the support membership of the
selected item, and the exact source cut at `first - q + p`.  It is still only
an input surface; later work must produce this record from actual Lemma 7.10
source/sample provenance or route failures to `ResidualBad`.  It is not yet
the outside-`E'` sample producer for `(7.62)`: `not E'`, center membership, and
current-scale endpoint localization remain separate source/sample facts.
-/
structure Lemma710OneCenterSourceRunSelectorInput
    (W : ℕ → Prop)
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (n J A : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P threshold q : ℕ)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (verticalGap : ℕ)
    (start : TaoSection7RenewalPoint) (p : ℕ)
    (S : Finset (ℕ × List TaoSection7RenewalPoint))
    (full : List TaoSection7RenewalPoint)
    (item : ℕ × List TaoSection7RenewalPoint) : Type where
  source_path :
    TaoSection7Case3FullWindowSourcePathData W pointAt n J A xi epsilon P
      threshold q j sourceHeight firstBlock sourceSuffixes
  start_eq :
    start = taoSection7SourceHitPoint j sourceHeight firstBlock
  point_q_eq : pointAt q = start.toPoint
  verticalGap_eq : old.cornerL - (pointAt q).l = (verticalGap : ℤ)
  item_mem : item ∈ S
  first : ℕ
  ledger :
    RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q first item.1 verticalGap start item.2
  source_cut :
    full =
      (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
        (first - q + p)
  source_cut_le : first - q + p ≤ sourceSuffixes.length

def lemma710OneCenterSourceRunSelectorInput_to_sourceCutCandidateData
    {W : ℕ → Prop}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap : ℕ}
    {start : TaoSection7RenewalPoint} {p : ℕ}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (h :
      Lemma710OneCenterSourceRunSelectorInput W PrefixOK pointAt n J A xi
        epsilon P threshold q j sourceHeight firstBlock sourceSuffixes old
        verticalGap start p S full item) :
    Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q verticalGap start p full item :=
  { first := h.first
    ledger := h.ledger
    source_cut := h.source_cut
    source_cut_le := h.source_cut_le }

theorem lemma710OneCenterSourceRunSelectorInput_item_mem
    {W : ℕ → Prop}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap : ℕ}
    {start : TaoSection7RenewalPoint} {p : ℕ}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (h :
      Lemma710OneCenterSourceRunSelectorInput W PrefixOK pointAt n J A xi
        epsilon P threshold q j sourceHeight firstBlock sourceSuffixes old
        verticalGap start p S full item) :
    item ∈ S :=
  h.item_mem

/--
Projection from source-run selector inputs to the `hselect` premise used by
`randomKSourcePrefixFamilyCoverage_of_sourceCutEndpointNearCenter`.

This does not prove the selector from endpoint geometry.  The premise must
still supply, for each source endpoint-near-center full list, either a source
construction residual or concrete source-run selector input.
-/
theorem lemma710OneCenter_hselect_of_sourceRunSelectorInput
    {W : ℕ → Prop}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap : ℕ}
    {start : TaoSection7RenewalPoint} {p : ℕ}
    {R : ℝ} {C : Finset TaoSection7Point}
    {ResidualBad : TaoSection7Point → List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hselector :
      ∀ c ∈ C, ∀ full,
        Lemma710SourceEndpointNearCenter start R c full →
          ResidualBad c full ∨
            ∃ item, Nonempty
              (Lemma710OneCenterSourceRunSelectorInput W PrefixOK pointAt n J A
                xi epsilon P threshold q j sourceHeight firstBlock
                sourceSuffixes old verticalGap start p S full item)) :
    ∀ c ∈ C, ∀ full,
      Lemma710SourceEndpointNearCenter start R c full →
        ResidualBad c full ∨
          ∃ item, item ∈ S ∧
            Nonempty
              (Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
                firstBlock sourceSuffixes old q verticalGap start p full item) := by
  intro c hc full hnear
  rcases hselector c hc full hnear with hres | hhit
  · exact Or.inl hres
  · rcases hhit with ⟨item, hinput⟩
    rcases hinput with ⟨hinput⟩
    exact
      Or.inr
        ⟨item, hinput.item_mem,
          ⟨lemma710OneCenterSourceRunSelectorInput_to_sourceCutCandidateData
            hinput⟩⟩

/--
One-center source-prefix coverage directly from source-run selector inputs.

This combines the source-run-selector projection with the fixed-horizon
one-center source-cut packaging theorem.  The actual source-run selector,
outside-`E'` sample provenance, residual exclusion, and source-law mass control
remain separate obligations.
-/
theorem randomKSourcePrefixFamilyCoverage_of_oneCenterSourceRunSelectorInput
    {W : ℕ → Prop}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap : ℕ}
    {start : TaoSection7RenewalPoint} {p : ℕ}
    {R : ℝ} {C : Finset TaoSection7Point}
    {ResidualBad : TaoSection7Point → List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hprefixes :
      RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start S)
    (hselector :
      ∀ c ∈ C, ∀ full,
        Lemma710SourceEndpointNearCenter start R c full →
          ResidualBad c full ∨
            ∃ item, Nonempty
              (Lemma710OneCenterSourceRunSelectorInput W PrefixOK pointAt n J A
                xi epsilon P threshold q j sourceHeight firstBlock
                sourceSuffixes old verticalGap start p S full item)) :
    ∀ c ∈ C,
      RandomKSourcePrefixFamilyCoverage PrefixOK
        (Lemma710SourceEndpointNearCenter start R c)
        (ResidualBad c)
        (Lemma710PostKEndpointNearCenter start p R c)
        S :=
  randomKSourcePrefixFamilyCoverage_of_sourceCutEndpointNearCenter hprefixes
    (lemma710OneCenter_hselect_of_sourceRunSelectorInput hselector)

/--
Build one selector input from a source-suffix vertical crossing and an explicit
source-cut oracle.

The first-passage ledger and canonical support membership are derived by the
existing random-`k` source-ledger constructor.  The source cut at
`first - q + p` remains an explicit input, matching the current hselect
frontier.
-/
theorem lemma710OneCenterSourceRunSelectorInput_of_sourceSuffixesCrossing_sourceCut
    {W : ℕ → Prop}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q N : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap : ℕ}
    {start : TaoSection7RenewalPoint} {p : ℕ}
    {full : List TaoSection7RenewalPoint}
    (hsource_path :
      TaoSection7Case3FullWindowSourcePathData W pointAt n J A xi epsilon P
        threshold q j sourceHeight firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hcross :
      start.l + (verticalGap : ℤ) <
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hsource_cut :
      ∀ (item : ℕ × List TaoSection7RenewalPoint) (first : ℕ),
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
          full =
            (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
              (first - q + p) ∧
            first - q + p ≤ sourceSuffixes.length) :
    ∃ item, Nonempty
      (Lemma710OneCenterSourceRunSelectorInput W PrefixOK pointAt n J A xi
        epsilon P threshold q j sourceHeight firstBlock sourceSuffixes old
        verticalGap start p
        (randomKVerticalFirstPassagePrefixFinset start verticalGap
          sourceSuffixes)
        full item) := by
  rcases exists_randomKSourceLedger_of_sourceSuffixes_crossing_at
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (start := start)
      hstart hpoint_q hverticalGap hNpos hNle hcross hpoint_first
      hprefix_ok with
    ⟨item, first, _hKleN, hledger⟩
  rcases hsource_cut item first hledger with ⟨hcut, hcut_le⟩
  refine ⟨item, ⟨?_⟩⟩
  exact
    { source_path := hsource_path
      start_eq := hstart
      point_q_eq := hpoint_q
      verticalGap_eq := hverticalGap
      item_mem := randomKSourceLedger_mem_verticalFirstPassagePrefixFinset
        hledger
      first := first
      ledger := hledger
      source_cut := hcut
      source_cut_le := hcut_le }

/--
Build one selector input from a source-suffix vertical crossing and post-`p`
room, for the canonical source cut `take (item.1 + p)`.

This removes the explicit source-cut oracle from
`lemma710OneCenterSourceRunSelectorInput_of_sourceSuffixesCrossing_sourceCut`
when the full list is the canonical post-room cut selected by the extracted
q-relative random `k`.  It still does not prove an event-to-sample selector,
endpoint-near-center membership, residual exclusion, or any source-law mass
control.
-/
theorem lemma710OneCenterSourceRunSelectorInput_of_sourceSuffixesCrossing_postRoom
    {W : ℕ → Prop}
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q N : ℕ}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {verticalGap : ℕ}
    {start : TaoSection7RenewalPoint} {p : ℕ}
    (hsource_path :
      TaoSection7Case3FullWindowSourcePathData W pointAt n J A xi epsilon P
        threshold q j sourceHeight firstBlock sourceSuffixes)
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hNpos : 0 < N)
    (hcross :
      start.l + (verticalGap : ℤ) <
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l)
    (hpost_room : N + p ≤ sourceSuffixes.length)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre)) :
    ∃ item, Nonempty
      (Lemma710OneCenterSourceRunSelectorInput W PrefixOK pointAt n J A xi
        epsilon P threshold q j sourceHeight firstBlock sourceSuffixes old
        verticalGap start p
        (randomKVerticalFirstPassagePrefixFinset start verticalGap
          sourceSuffixes)
        ((taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
          (item.1 + p))
        item) := by
  have hNle : N ≤ sourceSuffixes.length := by omega
  rcases exists_randomKSourceLedger_of_sourceSuffixes_crossing_at
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (start := start)
      hstart hpoint_q hverticalGap hNpos hNle hcross hpoint_first
      hprefix_ok with
    ⟨item, first, hKleN, hledger⟩
  have hhorizon : item.1 + p ≤ sourceSuffixes.length := by
    have hle : item.1 + p ≤ N + p := Nat.add_le_add_right hKleN p
    exact hle.trans hpost_room
  refine ⟨item, ⟨?_⟩⟩
  exact
    { source_path := hsource_path
      start_eq := hstart
      point_q_eq := hpoint_q
      verticalGap_eq := hverticalGap
      item_mem := randomKSourceLedger_mem_verticalFirstPassagePrefixFinset
        hledger
      first := first
      ledger := hledger
      source_cut := by
        simp [hledger.K_eq_first_sub_q]
      source_cut_le := by
        simpa [hledger.K_eq_first_sub_q] using hhorizon }

/--
The selected `k+p` endpoint lies on or above the old top row.

The proof uses the first-passage crossing at the stopped prefix `k`, then
propagates that inequality across the post-`k` tail by the positivity of Hold
increments.  This is intentionally separate from the outside-`E'` upper and
horizontal estimates.
-/
theorem lemma710SourceCutCandidateData_pointAt_first_add_p_lReal_lower
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hdata :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint) :
    (old.cornerL : ℝ) ≤ (pointAt (hdata.first + p)).lReal := by
  rcases lemma710SourceCutCandidateData_append_split hdata with
    ⟨tail, hfull, htail_len⟩
  have hgap :
      old.cornerL - start.l = (verticalGap : ℤ) := by
    simpa [hdata.ledger.point_q_eq, TaoSection7RenewalPoint.toPoint]
      using hdata.ledger.verticalGap_eq
  have hcorner : old.cornerL = start.l + (verticalGap : ℤ) := by
    omega
  have hcross :
      old.cornerL <
        (taoSection7RenewalPathPoint start item.2 item.1).l := by
    simpa [hcorner] using hdata.ledger.vertical_first.crosses
  let base := taoSection7RenewalPathPoint start item.2 item.1
  have htail_all : taoSection7AllHoldIncrementsLGeOne tail := by
    intro h hh
    have hfull_mem : h ∈ full := by
      rw [hfull]
      exact List.mem_append_right item.2 hh
    have hsource_mem :
        h ∈ taoSection7HoldIncrementsOfPrefixes sourceSuffixes := by
      rw [lemma710SourceCutCandidateData_full_eq_fixedHorizon hdata] at hfull_mem
      exact List.mem_of_mem_take hfull_mem
    exact taoSection7HoldIncrementsOfPrefixes_l_ge_one hsource_mem
  have htail_growth :
      base.l + (p : ℤ) ≤
        (taoSection7RenewalPathPoint base tail p).l :=
    taoSection7RenewalPathPoint_l_growth_ge_steps base tail p
      (by simp [htail_len]) htail_all
  have hbase_le_tail :
      (taoSection7RenewalPathPoint start item.2 item.1).l ≤
        (taoSection7RenewalPathPoint start full full.length).l := by
    have htail_nonneg : (0 : ℤ) ≤ (p : ℤ) := by exact_mod_cast Nat.zero_le p
    have hbase_le :
        base.l ≤ (taoSection7RenewalPathPoint base tail p).l := by
      linarith
    have hpath :
        taoSection7RenewalPathPoint start full full.length =
          taoSection7RenewalPathPoint base tail p := by
      have hitem_len : item.2.length = item.1 :=
        hdata.ledger.vertical_first.length_eq
      calc
        taoSection7RenewalPathPoint start full full.length =
            taoSection7RenewalPathPoint start (item.2 ++ tail)
              (item.2.length + p) := by
          simp [hfull, hitem_len, htail_len]
        _ = taoSection7RenewalPathPoint base tail p := by
          simpa [base, hitem_len] using
            renewalPathPoint_append_prefix_add start item.2 tail p
    simpa [base, hpath] using hbase_le
  have hendpoint :
      pointAt (hdata.first + p) =
        (taoSection7RenewalPathPoint start full full.length).toPoint :=
    lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint
      hdata hpoint_source
  have hold_le :
      (old.cornerL : ℤ) ≤
        (taoSection7RenewalPathPoint start full full.length).l := by
    exact le_trans hcross.le hbase_le_tail
  have hold_le_real :
      (old.cornerL : ℝ) ≤
        ((taoSection7RenewalPathPoint start full full.length).l : ℝ) := by
    exact_mod_cast hold_le
  simpa [hendpoint, TaoSection7Point.lReal, TaoSection7RenewalPoint.toPoint]
    using hold_le_real

/--
Source-facing outside-`E'` hit package tied to Tao Lemma 7.10's actual
`k+p` endpoint.

This is a pointwise anti-proxy surface: it requires the checked source-cut
datum for the selected random-`k` item and an explicit equality identifying
the endpoint with the `full.length` renewal endpoint of that source cut.  It
does not prove the outside-`E'` raw endpoint data, the finite center
membership, or any probability estimate.
-/
structure Lemma710OutsideEprimeKpEndpointSourceHitData
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap : ℕ)
    (start : TaoSection7RenewalPoint) (p : ℕ)
    (full : List TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (new : TaoSection7Triangle) (endpoint : TaoSection7Point)
    (C : Finset TaoSection7Point)
    (sMin gap Kgeo Bgeo J R : ℝ) : Type where
  item : ℕ × List TaoSection7RenewalPoint
  cut :
    Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start p full item
  endpoint_eq :
    endpoint =
      (taoSection7RenewalPathPoint start full full.length).toPoint
  source_hit :
    Lemma710OutsideEprimeSourceHitData family old new endpoint
      sMin gap Kgeo Bgeo J R
  anchor_mem_C : anchor old new ∈ C

theorem lemma710OutsideEprimeKpEndpointSourceHitData_endpoint_eq_sourcePrefixPath
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {C : Finset TaoSection7Point}
    {sMin gap Kgeo Bgeo J R : ℝ}
    (hdata :
      Lemma710OutsideEprimeKpEndpointSourceHitData PrefixOK pointAt
        j sourceHeight firstBlock sourceSuffixes old q verticalGap start p
        full family new endpoint C sMin gap Kgeo Bgeo J R) :
    endpoint =
      (taoSection7RenewalPathPoint start
        (taoSection7HoldIncrementsOfPrefixes sourceSuffixes)
        (hdata.item.1 + p)).toPoint := by
  calc
    endpoint =
        (taoSection7RenewalPathPoint start full full.length).toPoint :=
      hdata.endpoint_eq
    _ =
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes)
          (hdata.item.1 + p)).toPoint :=
      lemma710SourceCutCandidateData_fullEndpoint_toPoint_eq hdata.cut

theorem lemma710OutsideEprimeSourceHitData_of_kpEndpointSourceHitData
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {C : Finset TaoSection7Point}
    {sMin gap Kgeo Bgeo J R : ℝ}
    (hdata :
      Lemma710OutsideEprimeKpEndpointSourceHitData PrefixOK pointAt
        j sourceHeight firstBlock sourceSuffixes old q verticalGap start p
        full family new endpoint C sMin gap Kgeo Bgeo J R) :
    Lemma710OutsideEprimeSourceHitData family old new endpoint
        sMin gap Kgeo Bgeo J R ∧
      anchor old new ∈ C :=
  ⟨hdata.source_hit, hdata.anchor_mem_C⟩

def lemma710OutsideEprimeKpEndpointSourceHitData_of_rawEndpoint
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {C : Finset TaoSection7Point}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hendpoint :
      endpoint =
        (taoSection7RenewalPathPoint start full full.length).toPoint)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hold : old ∈ family) (hnew : new ∈ family) (hne : new ≠ old)
    (hsize : sMin ≤ new.size)
    (hJ : (Real.log 2 / Real.log 9) * (Kgeo * Bgeo + Kgeo * Bgeo) ≤ J)
    (hradius : J ^ 2 + (Kgeo * Bgeo) ^ 2 ≤ R ^ 2)
    (hraw :
      RawOutsideEprimeCommonPointEndpointData old new endpoint gap Kgeo Bgeo)
    (hanchor : anchor old new ∈ C) :
    Lemma710OutsideEprimeKpEndpointSourceHitData PrefixOK pointAt
      j sourceHeight firstBlock sourceSuffixes old q verticalGap start p full
      family new endpoint C sMin gap Kgeo Bgeo J R where
  item := item
  cut := hcut
  endpoint_eq := hendpoint
  source_hit :=
    { pairwiseDisjoint := hpair
      old_mem_family := hold
      new_mem_family := hnew
      new_ne_old := hne
      size_ge := hsize
      j_close_budget := hJ
      radius_absorbs := hradius
      raw_endpoint := hraw }
  anchor_mem_C := hanchor

def lemma710OutsideEprimeKpEndpointSourceHitData_of_rawPointAtFirstAddP
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {new : TaoSection7Triangle}
    {C : Finset TaoSection7Point}
    {sMin gap Kgeo Bgeo J R : ℝ}
    {item : ℕ × List TaoSection7RenewalPoint}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hold : old ∈ family) (hnew : new ∈ family) (hne : new ≠ old)
    (hsize : sMin ≤ new.size)
    (hJ : (Real.log 2 / Real.log 9) * (Kgeo * Bgeo + Kgeo * Bgeo) ≤ J)
    (hradius : J ^ 2 + (Kgeo * Bgeo) ^ 2 ≤ R ^ 2)
    (hraw :
      RawOutsideEprimeCommonPointEndpointData old new
        (pointAt (hcut.first + p)) gap Kgeo Bgeo)
    (hanchor : anchor old new ∈ C) :
    Lemma710OutsideEprimeKpEndpointSourceHitData PrefixOK pointAt
      j sourceHeight firstBlock sourceSuffixes old q verticalGap start p full
      family new (pointAt (hcut.first + p)) C sMin gap Kgeo Bgeo J R :=
  lemma710OutsideEprimeKpEndpointSourceHitData_of_rawEndpoint
    hcut
    (lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint
      hcut hpoint_source)
    hpair hold hnew hne hsize hJ hradius hraw hanchor

theorem lemma710OutsideEprimeSourceHitExists_of_nonempty_kpEndpointSourceHitData
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {C : Finset TaoSection7Point}
    {sMin gap Kgeo Bgeo J R : ℝ}
    (hdata :
      Nonempty
        (Lemma710OutsideEprimeKpEndpointSourceHitData PrefixOK pointAt
          j sourceHeight firstBlock sourceSuffixes old q verticalGap start p
          full family new endpoint C sMin gap Kgeo Bgeo J R)) :
    ∃ new : TaoSection7Triangle,
      Lemma710OutsideEprimeSourceHitData family old new endpoint
          sMin gap Kgeo Bgeo J R ∧
        anchor old new ∈ C := by
  rcases hdata with ⟨hdata⟩
  exact
    ⟨new,
      lemma710OutsideEprimeSourceHitData_of_kpEndpointSourceHitData hdata⟩

theorem lemma710OutsideEprimeKpEndpointSourceHitData_endpoint_eq_pointAt_first_add_p
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {new : TaoSection7Triangle} {endpoint : TaoSection7Point}
    {C : Finset TaoSection7Point}
    {sMin gap Kgeo Bgeo J R : ℝ}
    (hdata :
      Lemma710OutsideEprimeKpEndpointSourceHitData PrefixOK pointAt
        j sourceHeight firstBlock sourceSuffixes old q verticalGap start p
        full family new endpoint C sMin gap Kgeo Bgeo J R)
    (hpoint_source :
      ∀ N pre,
        N ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N →
            pointAt (q + N) =
              (taoSection7RenewalPathPoint start pre N).toPoint) :
    endpoint = pointAt (hdata.cut.first + p) := by
  have hpoint :
      pointAt (hdata.cut.first + p) =
        (taoSection7RenewalPathPoint start full full.length).toPoint :=
    lemma710SourceCutCandidateData_pointAt_first_add_p_eq_fullEndpoint
      hdata.cut hpoint_source
  exact hdata.endpoint_eq.trans hpoint.symm

/--
Event-facing row-data producer for the actual Lemma 7.10 `k+p` endpoint.

The large-triangle event supplies the new triangle and endpoint membership at
`pointAt (hcut.first + p)`.  The outside-`E'` endpoint estimates `(7.63)/(7.64)`
and the scalar old-row margin remain explicit hypotheses.
-/
theorem lemma710OutsideEprimeKpRowData_of_largeTriangleEndpointEstimates
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {sMin S Lerr Jerr gap : ℝ}
    (hcut :
      Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item)
    (hbase : old.Mem (pointAt q))
    (hS : S = ((old.cornerL - (pointAt q).l : ℤ) : ℝ))
    (hlarge :
      taoSection7Case3LargeTriangleEvent pointAt family
        (hcut.first + p) sMin)
    (hlower : (old.cornerL : ℝ) ≤ (pointAt (hcut.first + p)).lReal)
    (hupper :
      (pointAt (hcut.first + p)).lReal - (old.cornerL : ℝ) ≤ Lerr)
    (hj :
      |(pointAt (hcut.first + p)).jReal -
          ((pointAt q).jReal + S / 4)| ≤ Jerr)
    (hgap0 : 0 ≤ gap)
    (hL0 : 0 ≤ Lerr)
    (hJ0 : 0 ≤ Jerr)
    (hmargin :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))) :
    ∃ new : TaoSection7Triangle,
      new ∈ family ∧
        sMin ≤ new.size ∧
          OutsideEprimeBadLowerTipRowData old new (pointAt q)
            (pointAt (hcut.first + p)) S Lerr Jerr gap := by
  rcases hlarge with ⟨new, hnew_family, hnew_mem, hsize⟩
  exact
    ⟨new, hnew_family, hsize,
      outsideEprimeBadLowerTipRowData_of_endpoint_estimates
        hbase hnew_mem hS hlower hupper hj hgap0 hL0 hJ0 hmargin⟩

/--
Vertical constructor for the shared fixed-`p` source-run candidate.

This is still a vertical-branch producer: it consumes the explicit source-run
premise identifying the horizon-aware post-length with Tao's fixed `p`.  It
does not select the item into a non-singleton family `S` or prove headroom.
-/
theorem eprimeFixedPSourceRunCandidate_of_verticalSourceEvent
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap N p : ℕ}
    {start : TaoSection7RenewalPoint} {sourceThreshold : ℝ}
    {full : List TaoSection7RenewalPoint}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hthreshold_pos : 0 < sourceThreshold)
    (hfull :
      full = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N)
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hpost_eq :
      ∀ (item : ℕ × List TaoSection7RenewalPoint) (first postLength : ℕ),
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        full =
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
            (item.1 + postLength) →
        item.1 + postLength ≤ sourceSuffixes.length →
        postLength = p)
    (hsrc : EprimeVerticalSourceEvent start old sourceThreshold full) :
    ∃ item : ℕ × List TaoSection7RenewalPoint,
      EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item := by
  rcases eprimeVerticalSourceEvent_to_fixedPSourceLedgerCandidate
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (p := p) (start := start)
      (sourceThreshold := sourceThreshold) (full := full)
      hstart hpoint_q hverticalGap hthreshold_pos hfull hNpos hNle
      hpoint_first hprefix_ok hpost_eq hsrc with
    ⟨item, first, hledger, hfull_fixed, hhorizon⟩
  exact
    ⟨item,
      { ledger := ⟨first, hledger⟩
        full_eq := hfull_fixed
        horizon_le := hhorizon }⟩

/--
Vertical fixed-`p` source-run candidate from an exact source-horizon equation.

This is the sharper source-run boundary for the fixed-`p` premise: instead of
assuming a generic post-length oracle, it asks the source construction to prove
that the fixed event horizon `N` is exactly `K+p` for the extracted
first-passage item.
-/
theorem eprimeFixedPSourceRunCandidate_of_verticalSourceEvent_horizonEq
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap N p : ℕ}
    {start : TaoSection7RenewalPoint} {sourceThreshold : ℝ}
    {full : List TaoSection7RenewalPoint}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hthreshold_pos : 0 < sourceThreshold)
    (hfull :
      full = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N)
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hfixed_horizon :
      ∀ (item : ℕ × List TaoSection7RenewalPoint) (first : ℕ),
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        N = item.1 + p)
    (hsrc : EprimeVerticalSourceEvent start old sourceThreshold full) :
    ∃ item : ℕ × List TaoSection7RenewalPoint,
      EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item := by
  have hcross :
      start.l + (verticalGap : ℤ) <
        (taoSection7RenewalPathPoint start
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes) N).l :=
    eprimeVerticalSourceEvent_horizon_crosses hpoint_q hverticalGap
      hthreshold_pos hfull hNle hsrc
  rcases exists_randomKSourceLedger_of_sourceSuffixes_crossing_at
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (start := start)
      hstart hpoint_q hverticalGap hNpos hNle hcross hpoint_first
      hprefix_ok with
    ⟨item, first, _hKleN, hledger⟩
  have hN_eq : N = item.1 + p := hfixed_horizon item first hledger
  exact
    ⟨item,
      { ledger := ⟨first, hledger⟩
        full_eq := by
          simpa [hN_eq] using hfull
        horizon_le := by
          simpa [hN_eq] using hNle }⟩

/--
Vertical fixed-`p` source-run candidate from the source event cut at
`first - q + p`.

This consumes the source-shaped cut identity for each extracted ledger and
derives the fixed horizon equation with
`randomKSourceLedger_fixedHorizonEq_of_full_first_add_p`.
-/
theorem eprimeFixedPSourceRunCandidate_of_verticalSourceEvent_sourceCut
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap N p : ℕ}
    {start : TaoSection7RenewalPoint} {sourceThreshold : ℝ}
    {full : List TaoSection7RenewalPoint}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hthreshold_pos : 0 < sourceThreshold)
    (hfull :
      full = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take N)
    (hNpos : 0 < N)
    (hNle : N ≤ sourceSuffixes.length)
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hsource_cut :
      ∀ (item : ℕ × List TaoSection7RenewalPoint) (first : ℕ),
        RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
          sourceSuffixes old q first item.1 verticalGap start item.2 →
        full =
          (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
            (first - q + p) ∧
          first - q + p ≤ sourceSuffixes.length)
    (hsrc : EprimeVerticalSourceEvent start old sourceThreshold full) :
    ∃ item : ℕ × List TaoSection7RenewalPoint,
      EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item := by
  refine eprimeFixedPSourceRunCandidate_of_verticalSourceEvent_horizonEq
      (PrefixOK := PrefixOK) (pointAt := pointAt) (j := j)
      (sourceHeight := sourceHeight) (firstBlock := firstBlock)
      (sourceSuffixes := sourceSuffixes) (old := old) (q := q)
      (verticalGap := verticalGap) (N := N) (p := p) (start := start)
      (sourceThreshold := sourceThreshold) (full := full)
      hstart hpoint_q hverticalGap hthreshold_pos hfull hNpos hNle
      hpoint_first hprefix_ok ?_ hsrc
  intro item first hledger
  rcases hsource_cut item first hledger with ⟨hfullFirstP, hfirstP_le⟩
  exact
    randomKSourceLedger_fixedHorizonEq_of_full_first_add_p
      hledger hfull hNle hfullFirstP hfirstP_le

/--
Every shared fixed-`p` source-run candidate belongs to the concrete finite
source-suffix vertical first-passage family.
-/
theorem eprimeFixedPSourceRunCandidate_mem_verticalFirstPassagePrefixFinset
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap p : ℕ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {item : ℕ × List TaoSection7RenewalPoint}
    (h :
      EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start p full item) :
    item ∈
      randomKVerticalFirstPassagePrefixFinset start verticalGap
        sourceSuffixes := by
  rcases h.ledger with ⟨first, hledger⟩
  exact randomKSourceLedger_mem_verticalFirstPassagePrefixFinset hledger

/--
Post-`k` vertical tail event corresponding to the vertical piece of `E'`.

This is the tail predicate that should be bounded by the stopped-tail input;
it is separate from outside-`E'` one-center localization.
-/
def EprimeVerticalTailEvent
    (start : TaoSection7RenewalPoint) (p : ℕ) (tailThreshold : ℝ)
    (pre tail : List TaoSection7RenewalPoint) : Prop :=
  tail.length = p ∧
    tailThreshold ≤
      (((lemma710PostKTailEndpoint start p pre tail).l -
        (lemma710StoppedPrefixEndpoint start pre).l : ℤ) : ℝ)

theorem eprimeVerticalTailEvent_iff_tailDisplacement
    {start : TaoSection7RenewalPoint} {p : ℕ} {tailThreshold : ℝ}
    {pre tail : List TaoSection7RenewalPoint} :
    EprimeVerticalTailEvent start p tailThreshold pre tail ↔
      Lemma710VerticalTailDisplacementEvent
        (lemma710StoppedPrefixEndpoint start pre) p tailThreshold tail := by
  simp [EprimeVerticalTailEvent, Lemma710VerticalTailDisplacementEvent,
    lemma710PostKTailEndpoint_eq_tailPath]

/--
Deterministic reduction from the full vertical `E'` event to the post-`k`
vertical tail event, once the stopped prefix endpoint has enough headroom below
the full source threshold.

The prefix-headroom hypothesis is the source fact still needed from Tao's
first-passage and residual split; this theorem only performs the arithmetic
transport through a concrete append decomposition.
-/
theorem eprimeVerticalTailEvent_of_sourceEvent_append
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {sourceThreshold tailThreshold : ℝ} {p : ℕ}
    {full pre tail : List TaoSection7RenewalPoint}
    (hfull : full = pre ++ tail)
    (htail : tail.length = p)
    (hprefix :
      (((lemma710StoppedPrefixEndpoint start pre).l -
        old.cornerL : ℤ) : ℝ) ≤ sourceThreshold - tailThreshold)
    (hsrc : EprimeVerticalSourceEvent start old sourceThreshold full) :
    EprimeVerticalTailEvent start p tailThreshold pre tail := by
  subst full
  constructor
  · exact htail
  · dsimp [EprimeVerticalSourceEvent, EprimeVerticalTailEvent,
      lemma710PostKTailEndpoint, lemma710StoppedPrefixEndpoint] at hprefix hsrc ⊢
    simp [List.length_append, htail] at hsrc ⊢
    let endpoint :=
      taoSection7RenewalPathPoint start (pre ++ tail) (pre.length + p)
    let base := taoSection7RenewalPathPoint start pre pre.length
    change
      tailThreshold ≤
        (endpoint.l : ℝ) - (base.l : ℝ)
    change
      sourceThreshold ≤
        (endpoint.l : ℝ) - (old.cornerL : ℝ) at hsrc
    have hprefix' :
        (base.l : ℝ) - (old.cornerL : ℝ) ≤
          sourceThreshold - tailThreshold := by
      change ((base.l - old.cornerL : ℤ) : ℝ) ≤
        sourceThreshold - tailThreshold at hprefix
      norm_num at hprefix ⊢
      exact hprefix
    nlinarith

/--
Horizontal part of Tao's exceptional event `E'`, stated on a full source-side
Hold-increment list.

The center is an absolute horizontal lattice coordinate.  The later source
layer should instantiate Tao's center as `start.j + s / 4`, not as a
standalone relative `s / 4`; the threshold remains explicit for the
`s ^ 0.6` scale.
-/
def EprimeHorizontalSourceEvent
    (start : TaoSection7RenewalPoint)
    (horizontalCenter sourceThreshold : ℝ)
    (full : List TaoSection7RenewalPoint) : Prop :=
  sourceThreshold ≤
    |(((taoSection7RenewalPathPoint start full full.length).j : ℕ) : ℝ) -
      horizontalCenter|

/--
Post-`k` horizontal tail event corresponding to the horizontal piece of `E'`.
-/
def EprimeHorizontalTailEvent
    (start : TaoSection7RenewalPoint) (p : ℕ) (tailThreshold : ℝ)
    (pre tail : List TaoSection7RenewalPoint) : Prop :=
  tail.length = p ∧
    tailThreshold ≤
      |(((lemma710PostKTailEndpoint start p pre tail).j : ℕ) : ℝ) -
        (((lemma710StoppedPrefixEndpoint start pre).j : ℕ) : ℝ)|

theorem eprimeHorizontalTailEvent_iff_tailDisplacement
    {start : TaoSection7RenewalPoint} {p : ℕ} {tailThreshold : ℝ}
    {pre tail : List TaoSection7RenewalPoint} :
    EprimeHorizontalTailEvent start p tailThreshold pre tail ↔
      Lemma710HorizontalTailDisplacementEvent
        (lemma710StoppedPrefixEndpoint start pre) p tailThreshold tail := by
  simp [EprimeHorizontalTailEvent, Lemma710HorizontalTailDisplacementEvent,
    lemma710PostKTailEndpoint_eq_tailPath]

/--
Deterministic reduction from the full horizontal `E'` event to the post-`k`
horizontal tail event, assuming the stopped prefix endpoint is still close to
the horizontal source center.
-/
theorem eprimeHorizontalTailEvent_of_sourceEvent_append
    {start : TaoSection7RenewalPoint}
    {horizontalCenter sourceThreshold tailThreshold : ℝ} {p : ℕ}
    {full pre tail : List TaoSection7RenewalPoint}
    (hfull : full = pre ++ tail)
    (htail : tail.length = p)
    (hprefix :
      |(((lemma710StoppedPrefixEndpoint start pre).j : ℕ) : ℝ) -
        horizontalCenter| ≤ sourceThreshold - tailThreshold)
    (hsrc :
      EprimeHorizontalSourceEvent start horizontalCenter sourceThreshold full) :
    EprimeHorizontalTailEvent start p tailThreshold pre tail := by
  subst full
  constructor
  · exact htail
  · dsimp [EprimeHorizontalSourceEvent, EprimeHorizontalTailEvent,
      lemma710PostKTailEndpoint, lemma710StoppedPrefixEndpoint] at hprefix hsrc ⊢
    simp [List.length_append, htail] at hsrc ⊢
    let endpoint :=
      (((taoSection7RenewalPathPoint start (pre ++ tail)
        (pre.length + p)).j : ℕ) : ℝ)
    let base :=
      (((taoSection7RenewalPathPoint start pre pre.length).j : ℕ) : ℝ)
    change tailThreshold ≤ |endpoint - base|
    change sourceThreshold ≤ |endpoint - horizontalCenter| at hsrc
    change |base - horizontalCenter| ≤
      sourceThreshold - tailThreshold at hprefix
    have htriangle :
        |endpoint - horizontalCenter| ≤
          |endpoint - base| + |base - horizontalCenter| := by
      calc
        |endpoint - horizontalCenter| =
            |(endpoint - base) + (base - horizontalCenter)| := by ring_nf
        _ ≤ |endpoint - base| + |base - horizontalCenter| :=
            abs_add_le (endpoint - base) (base - horizontalCenter)
    nlinarith

/--
Concrete source-coverage input for the vertical `E'` tail.

This is still a source-run coverage hypothesis, not a probability estimate:
the residual predicate and its mass control remain separate later obligations.
-/
structure EprimeVerticalSourceCoverage
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (sourceThreshold tailThreshold : ℝ) (p : ℕ)
    (ResidualBad : List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  prefixes : RandomKSourceLedgerFamily PrefixOK S
  cover_or_residual :
    ∀ full, EprimeVerticalSourceEvent start old sourceThreshold full →
      ResidualBad full ∨
        ∃ item, item ∈ S ∧
          ∃ tail : List TaoSection7RenewalPoint,
            full = item.2 ++ tail ∧
              EprimeVerticalTailEvent start p tailThreshold item.2 tail

theorem eprimeVerticalSourceCoverage_to_randomKSourcePrefixFamilyCoverage
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {sourceThreshold tailThreshold : ℝ} {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      EprimeVerticalSourceCoverage PrefixOK start old sourceThreshold
        tailThreshold p ResidualBad S) :
    RandomKSourcePrefixFamilyCoverage PrefixOK
      (EprimeVerticalSourceEvent start old sourceThreshold)
      ResidualBad
      (EprimeVerticalTailEvent start p tailThreshold)
      S where
  prefixes := h.prefixes
  event_cover_or_residual := h.cover_or_residual

/--
Build vertical `E'` source coverage from a selected random-`k` split plus
prefix headroom.

The split hypothesis is the first source-run producer shape needed next: every
vertical source event is either residual, or has a selected stopped prefix,
an append decomposition, the post-`k` tail length, and enough prefix headroom
to reduce the event to the post-`k` vertical tail.
-/
theorem eprimeVerticalSourceCoverage_of_selectedSplit
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {sourceThreshold tailThreshold : ℝ} {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hprefixes : RandomKSourceLedgerFamily PrefixOK S)
    (hselected :
      ∀ full, EprimeVerticalSourceEvent start old sourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            ∃ tail : List TaoSection7RenewalPoint,
              full = item.2 ++ tail ∧
                tail.length = p ∧
                  (((lemma710StoppedPrefixEndpoint start item.2).l -
                    old.cornerL : ℤ) : ℝ) ≤
                    sourceThreshold - tailThreshold) :
    EprimeVerticalSourceCoverage PrefixOK start old sourceThreshold
      tailThreshold p ResidualBad S where
  prefixes := hprefixes
  cover_or_residual := by
    intro full hsrc
    rcases hselected full hsrc with hres | hsplit
    · exact Or.inl hres
    · rcases hsplit with ⟨item, hitem, tail, hfull, htail, hheadroom⟩
      exact Or.inr
        ⟨item, hitem, tail, hfull,
          eprimeVerticalTailEvent_of_sourceEvent_append
            hfull htail hheadroom hsrc⟩

/--
Concrete source-coverage input for the horizontal `E'` tail.

This is intentionally separate from the vertical coverage input and from the
outside-`E'` one-center localization layer.
-/
structure EprimeHorizontalSourceCoverage
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (start : TaoSection7RenewalPoint)
    (horizontalCenter sourceThreshold tailThreshold : ℝ) (p : ℕ)
    (ResidualBad : List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  prefixes : RandomKSourceLedgerFamily PrefixOK S
  cover_or_residual :
    ∀ full,
      EprimeHorizontalSourceEvent start horizontalCenter sourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            ∃ tail : List TaoSection7RenewalPoint,
              full = item.2 ++ tail ∧
                EprimeHorizontalTailEvent start p tailThreshold item.2 tail

theorem eprimeHorizontalSourceCoverage_to_randomKSourcePrefixFamilyCoverage
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter sourceThreshold tailThreshold : ℝ} {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      EprimeHorizontalSourceCoverage PrefixOK start horizontalCenter
        sourceThreshold tailThreshold p ResidualBad S) :
    RandomKSourcePrefixFamilyCoverage PrefixOK
      (EprimeHorizontalSourceEvent start horizontalCenter sourceThreshold)
      ResidualBad
      (EprimeHorizontalTailEvent start p tailThreshold)
      S where
  prefixes := h.prefixes
  event_cover_or_residual := h.cover_or_residual

/--
Build horizontal `E'` source coverage from a selected random-`k` split plus
prefix headroom.

The horizontal center is an absolute `j` coordinate.  The Tao instantiation
should pass the source start shifted by the horizontal source offset, not a
standalone relative offset.
-/
theorem eprimeHorizontalSourceCoverage_of_selectedSplit
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter sourceThreshold tailThreshold : ℝ} {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hprefixes : RandomKSourceLedgerFamily PrefixOK S)
    (hselected :
      ∀ full,
        EprimeHorizontalSourceEvent start horizontalCenter sourceThreshold full →
          ResidualBad full ∨
            ∃ item, item ∈ S ∧
              ∃ tail : List TaoSection7RenewalPoint,
                full = item.2 ++ tail ∧
                  tail.length = p ∧
                    |(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                      horizontalCenter| ≤
                      sourceThreshold - tailThreshold) :
    EprimeHorizontalSourceCoverage PrefixOK start horizontalCenter
      sourceThreshold tailThreshold p ResidualBad S where
  prefixes := hprefixes
  cover_or_residual := by
    intro full hsrc
    rcases hselected full hsrc with hres | hsplit
    · exact Or.inl hres
    · rcases hsplit with ⟨item, hitem, tail, hfull, htail, hheadroom⟩
      exact Or.inr
        ⟨item, hitem, tail, hfull,
          eprimeHorizontalTailEvent_of_sourceEvent_append
            hfull htail hheadroom hsrc⟩

/--
Source-facing selected split for the `E'` alternatives in Lemma 7.10.

This is a deterministic routing surface, not a mass estimate.  `ResidualBad`
records failures before a selected post-`k` tail event is available, such as
source-domain or prefix-headroom failures; failure of the post-`k` tail bound
belongs on the selected tail-event side.
-/
structure EprimeSelectedSourceSplit
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (start : TaoSection7RenewalPoint) (old : TaoSection7Triangle)
    (horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ)
    (p : ℕ)
    (ResidualBad : List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  prefixes : RandomKSourceLedgerFamily PrefixOK S
  vertical_selected :
    ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
      ResidualBad full ∨
        ∃ item, item ∈ S ∧
          ∃ tail : List TaoSection7RenewalPoint,
            full = item.2 ++ tail ∧
              tail.length = p ∧
                (((lemma710StoppedPrefixEndpoint start item.2).l -
                  old.cornerL : ℤ) : ℝ) ≤
                  verticalSourceThreshold - verticalTailThreshold
  horizontal_selected :
    ∀ full,
      EprimeHorizontalSourceEvent start horizontalCenter horizontalSourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            ∃ tail : List TaoSection7RenewalPoint,
              full = item.2 ++ tail ∧
                tail.length = p ∧
                  |(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                    horizontalCenter| ≤
                    horizontalSourceThreshold - horizontalTailThreshold

/--
Fixed-source version of the `E'` selected split.

The selected fields are the same as in `EprimeSelectedSourceSplit`, but the
prefix family now records one shared source datum for all selected ledgers.
This is still a routing surface, not a proof of the source-run split or a
probability estimate.
-/
structure EprimeFixedSourceSelectedSplit
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap : ℕ)
    (start : TaoSection7RenewalPoint)
    (horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ)
    (p : ℕ)
    (ResidualBad : List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  prefixes :
    RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q verticalGap start S
  vertical_selected :
    ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
      ResidualBad full ∨
        ∃ item, item ∈ S ∧
          ∃ tail : List TaoSection7RenewalPoint,
            full = item.2 ++ tail ∧
              tail.length = p ∧
                (((lemma710StoppedPrefixEndpoint start item.2).l -
                  old.cornerL : ℤ) : ℝ) ≤
                  verticalSourceThreshold - verticalTailThreshold
  horizontal_selected :
    ∀ full,
      EprimeHorizontalSourceEvent start horizontalCenter horizontalSourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            ∃ tail : List TaoSection7RenewalPoint,
              full = item.2 ++ tail ∧
                tail.length = p ∧
                  |(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                    horizontalCenter| ≤
                    horizontalSourceThreshold - horizontalTailThreshold

/--
Fixed-source selector/headroom input for the `E'` selected split.

Compared with `EprimeFixedSourceSelectedSplit`, this surface does not ask the
source-run theorem to provide the append decomposition and tail length
directly.  It asks for the selected item, the fixed full source list, the
fixed horizon equation, and the relevant prefix headroom; the checked ledger
split then supplies `full = item.2 ++ tail` and `tail.length = p`.
-/
structure EprimeFixedSourceHeadroomSelector
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap : ℕ)
    (start : TaoSection7RenewalPoint)
    (horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ)
    (p : ℕ)
    (ResidualBad : List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  prefixes :
    RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q verticalGap start S
  vertical_selected :
    ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
      ResidualBad full ∨
        ∃ item, item ∈ S ∧
          full = taoSection7HoldIncrementsOfPrefixes sourceSuffixes ∧
            p = sourceSuffixes.length - item.1 ∧
              (((lemma710StoppedPrefixEndpoint start item.2).l -
                old.cornerL : ℤ) : ℝ) ≤
                verticalSourceThreshold - verticalTailThreshold
  horizontal_selected :
    ∀ full,
      EprimeHorizontalSourceEvent start horizontalCenter horizontalSourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            full = taoSection7HoldIncrementsOfPrefixes sourceSuffixes ∧
              p = sourceSuffixes.length - item.1 ∧
                |(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                  horizontalCenter| ≤
                  horizontalSourceThreshold - horizontalTailThreshold

/--
Fixed-horizon selector/headroom input for the `E'` selected split.

This is the source-run-facing variant of
`EprimeFixedSourceHeadroomSelector`: the full source event is allowed to be
the fixed `K+p` horizon cut out of a longer remaining source suffix list.
The checked split helper then supplies the append decomposition and length-`p`
tail for the downstream selected split.
-/
structure EprimeFixedHorizonHeadroomSelector
    (PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (sourceHeight : ℕ) (firstBlock : List ℕ)
    (sourceSuffixes : List (List ℕ))
    (old : TaoSection7Triangle) (q verticalGap : ℕ)
    (start : TaoSection7RenewalPoint)
    (horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ)
    (p : ℕ)
    (ResidualBad : List TaoSection7RenewalPoint → Prop)
    (S : Finset (ℕ × List TaoSection7RenewalPoint)) : Prop where
  prefixes :
    RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q verticalGap start S
  vertical_selected :
    ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
      ResidualBad full ∨
        ∃ item, item ∈ S ∧
          full =
            (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
              (item.1 + p) ∧
            item.1 + p ≤ sourceSuffixes.length ∧
              (((lemma710StoppedPrefixEndpoint start item.2).l -
                old.cornerL : ℤ) : ℝ) ≤
                verticalSourceThreshold - verticalTailThreshold
  horizontal_selected :
    ∀ full,
      EprimeHorizontalSourceEvent start horizontalCenter horizontalSourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            full =
              (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
                (item.1 + p) ∧
              item.1 + p ≤ sourceSuffixes.length ∧
                |(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                  horizontalCenter| ≤
                  horizontalSourceThreshold - horizontalTailThreshold

/--
Build the fixed-horizon selector/headroom input from a candidate selector plus
residual guards for prefix-headroom failure.

This is the producer-facing fixed-horizon target: the hard source-run theorem
still has to select the item, identify the `K+p` source horizon, and either
prove prefix headroom or put the source event into `ResidualBad`.
-/
theorem eprimeFixedHorizonHeadroomSelector_of_candidate_or_residual
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hprefixes :
      RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start S)
    (hvertical :
      ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            full =
              (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
                (item.1 + p) ∧
              item.1 + p ≤ sourceSuffixes.length ∧
                (¬ ((((lemma710StoppedPrefixEndpoint start item.2).l -
                    old.cornerL : ℤ) : ℝ) ≤
                    verticalSourceThreshold - verticalTailThreshold) →
                  ResidualBad full))
    (hhorizontal :
      ∀ full,
        EprimeHorizontalSourceEvent start horizontalCenter
          horizontalSourceThreshold full →
          ResidualBad full ∨
            ∃ item, item ∈ S ∧
              full =
                (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
                  (item.1 + p) ∧
                item.1 + p ≤ sourceSuffixes.length ∧
                  (¬ (|(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                      horizontalCenter| ≤
                      horizontalSourceThreshold - horizontalTailThreshold) →
                    ResidualBad full)) :
    EprimeFixedHorizonHeadroomSelector PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start horizontalCenter
      verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
      horizontalTailThreshold p ResidualBad S where
  prefixes := hprefixes
  vertical_selected := by
    classical
    intro full hsrc
    rcases hvertical full hsrc with hres | hcandidate
    · exact Or.inl hres
    · rcases hcandidate with
        ⟨item, hitem, hfull, hhorizon, hresidual_of_not_headroom⟩
      by_cases hheadroom :
          (((lemma710StoppedPrefixEndpoint start item.2).l -
            old.cornerL : ℤ) : ℝ) ≤
            verticalSourceThreshold - verticalTailThreshold
      · exact Or.inr ⟨item, hitem, hfull, hhorizon, hheadroom⟩
      · exact Or.inl (hresidual_of_not_headroom hheadroom)
  horizontal_selected := by
    classical
    intro full hsrc
    rcases hhorizontal full hsrc with hres | hcandidate
    · exact Or.inl hres
    · rcases hcandidate with
        ⟨item, hitem, hfull, hhorizon, hresidual_of_not_headroom⟩
      by_cases hheadroom :
          |(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
            horizontalCenter| ≤
            horizontalSourceThreshold - horizontalTailThreshold
      · exact Or.inr ⟨item, hitem, hfull, hhorizon, hheadroom⟩
      · exact Or.inl (hresidual_of_not_headroom hheadroom)

/--
Build the fixed-horizon selector from pointwise source ledgers and the
candidate selector fields.

This is the finite-family boundary after
`exists_randomKSourceLedger_of_sourceSuffixes_crossing`: the pointwise ledger
producer and aggregate prefix-mass bound are explicit, and event-to-item
selection/horizon/headroom remain explicit inputs.
-/
theorem eprimeFixedHorizonHeadroomSelector_of_sourceLedgerCandidates
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hledger :
      ∀ item, item ∈ S →
        ∃ first : ℕ,
          RandomKSourceLedger PrefixOK pointAt j sourceHeight firstBlock
            sourceSuffixes old q first item.1 verticalGap start item.2)
    (hmass :
      (∑ item ∈ S, (taoSection7HoldListPMF item.1 item.2).toReal) ≤ 1)
    (hvertical :
      ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            full =
              (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
                (item.1 + p) ∧
              item.1 + p ≤ sourceSuffixes.length ∧
                (¬ ((((lemma710StoppedPrefixEndpoint start item.2).l -
                    old.cornerL : ℤ) : ℝ) ≤
                    verticalSourceThreshold - verticalTailThreshold) →
                  ResidualBad full))
    (hhorizontal :
      ∀ full,
        EprimeHorizontalSourceEvent start horizontalCenter
          horizontalSourceThreshold full →
          ResidualBad full ∨
            ∃ item, item ∈ S ∧
              full =
                (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take
                  (item.1 + p) ∧
                item.1 + p ≤ sourceSuffixes.length ∧
                  (¬ (|(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                      horizontalCenter| ≤
                      horizontalSourceThreshold - horizontalTailThreshold) →
                    ResidualBad full)) :
    EprimeFixedHorizonHeadroomSelector PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start horizontalCenter
      verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
      horizontalTailThreshold p ResidualBad S :=
  eprimeFixedHorizonHeadroomSelector_of_candidate_or_residual
    (hprefixes :=
      { ledger := hledger
        mass_le_one := hmass })
    hvertical hhorizontal

/--
Build the fixed-horizon selector from shared source-run candidates.

This is the non-singleton route boundary: `S` membership, residual routing, and
headroom failure remain explicit, while each selected item carries the common
fixed-`p` ledger/horizon package used by both `E'` branches.
-/
theorem eprimeFixedHorizonHeadroomSelector_of_routeCandidates
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hprefixes :
      RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start S)
    (hvertical :
      ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
              firstBlock sourceSuffixes old q verticalGap start p full item ∧
              (¬ ((((lemma710StoppedPrefixEndpoint start item.2).l -
                  old.cornerL : ℤ) : ℝ) ≤
                  verticalSourceThreshold - verticalTailThreshold) →
                ResidualBad full))
    (hhorizontal :
      ∀ full,
        EprimeHorizontalSourceEvent start horizontalCenter
          horizontalSourceThreshold full →
          ResidualBad full ∨
            ∃ item, item ∈ S ∧
              EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
                firstBlock sourceSuffixes old q verticalGap start p full item ∧
                (¬ (|(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                    horizontalCenter| ≤
                    horizontalSourceThreshold - horizontalTailThreshold) →
                  ResidualBad full)) :
    EprimeFixedHorizonHeadroomSelector PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start horizontalCenter
      verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
      horizontalTailThreshold p ResidualBad S :=
  eprimeFixedHorizonHeadroomSelector_of_candidate_or_residual
    (hprefixes := hprefixes)
    (hvertical := by
      intro full hsrc
      rcases hvertical full hsrc with hres | hcandidate
      · exact Or.inl hres
      · rcases hcandidate with
          ⟨item, hitem, hcandidate, hresidual_of_not_headroom⟩
        exact
          Or.inr
            ⟨item, hitem, hcandidate.full_eq, hcandidate.horizon_le,
              hresidual_of_not_headroom⟩)
    (hhorizontal := by
      intro full hsrc
      rcases hhorizontal full hsrc with hres | hcandidate
      · exact Or.inl hres
      · rcases hcandidate with
          ⟨item, hitem, hcandidate, hresidual_of_not_headroom⟩
        exact
          Or.inr
            ⟨item, hitem, hcandidate.full_eq, hcandidate.horizon_le,
              hresidual_of_not_headroom⟩)

/--
Build the fixed-horizon selector from branch candidates that still expose
their source-cut provenance.

The branch-facing premise is intentionally stronger than
`EprimeFixedPSourceRunCandidate`: it must produce nonempty
`Lemma710SourceCutCandidateData`, and only this wrapper projects that data to
the consumer-facing fixed-`p` candidate.  This prevents later vertical or
horizontal branch producers from bypassing the shared source cut
`full = take (first - q + p)` by returning a bare horizon candidate.
-/
theorem eprimeFixedHorizonHeadroomSelector_of_sourceCutDataRouteCandidates
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hprefixes :
      RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start S)
    (hvertical :
      ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            Nonempty
              (Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
                firstBlock sourceSuffixes old q verticalGap start p full item) ∧
              (¬ ((((lemma710StoppedPrefixEndpoint start item.2).l -
                  old.cornerL : ℤ) : ℝ) ≤
                  verticalSourceThreshold - verticalTailThreshold) →
                ResidualBad full))
    (hhorizontal :
      ∀ full,
        EprimeHorizontalSourceEvent start horizontalCenter
          horizontalSourceThreshold full →
          ResidualBad full ∨
            ∃ item, item ∈ S ∧
              Nonempty
                (Lemma710SourceCutCandidateData PrefixOK pointAt j sourceHeight
                  firstBlock sourceSuffixes old q verticalGap start p full item) ∧
                (¬ (|(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                    horizontalCenter| ≤
                    horizontalSourceThreshold - horizontalTailThreshold) →
                  ResidualBad full)) :
    EprimeFixedHorizonHeadroomSelector PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start horizontalCenter
      verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
      horizontalTailThreshold p ResidualBad S :=
  eprimeFixedHorizonHeadroomSelector_of_routeCandidates
    (hprefixes := hprefixes)
    (hvertical := by
      intro full hsrc
      rcases hvertical full hsrc with hres | hcandidate
      · exact Or.inl hres
      · rcases hcandidate with
          ⟨item, hitem, hdata, hresidual_of_not_headroom⟩
        rcases hdata with ⟨hdata⟩
        exact
          Or.inr
            ⟨item, hitem,
              lemma710SourceCutCandidateData_to_fixedPSourceRunCandidate
                hdata,
              hresidual_of_not_headroom⟩)
    (hhorizontal := by
      intro full hsrc
      rcases hhorizontal full hsrc with hres | hcandidate
      · exact Or.inl hres
      · rcases hcandidate with
          ⟨item, hitem, hdata, hresidual_of_not_headroom⟩
        rcases hdata with ⟨hdata⟩
        exact
          Or.inr
            ⟨item, hitem,
              lemma710SourceCutCandidateData_to_fixedPSourceRunCandidate
                hdata,
              hresidual_of_not_headroom⟩)

/--
Build the fixed-horizon selector using the concrete finite family of
source-suffix vertical first-passage prefixes.

This removes the selected-item membership premise from the vertical and
horizontal branch producers: any returned `EprimeFixedPSourceRunCandidate`
already carries a ledger, and every such ledger belongs to
`randomKVerticalFirstPassagePrefixFinset`.  The aggregate prefix-mass bound and
headroom/residual guards remain explicit.
-/
theorem eprimeFixedHorizonHeadroomSelector_of_verticalFirstPassageRouteCandidates
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    (hstart :
      start = taoSection7SourceHitPoint j sourceHeight firstBlock)
    (hpoint_q : pointAt q = start.toPoint)
    (hverticalGap :
      old.cornerL - (pointAt q).l = (verticalGap : ℤ))
    (hpoint_first :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            pointAt (q + K) =
              (taoSection7RenewalPathPoint start pre K).toPoint)
    (hprefix_ok :
      ∀ K pre,
        K ≤ sourceSuffixes.length →
          pre = (taoSection7HoldIncrementsOfPrefixes sourceSuffixes).take K →
            VerticalFirstPassagePrefix start verticalGap K pre →
              PrefixOK (K, pre))
    (hmass :
      (∑ item ∈
        randomKVerticalFirstPassagePrefixFinset start verticalGap sourceSuffixes,
        (taoSection7HoldListPMF item.1 item.2).toReal) ≤ 1)
    (hvertical :
      ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
        ResidualBad full ∨
          ∃ item,
            EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
              firstBlock sourceSuffixes old q verticalGap start p full item ∧
              (¬ ((((lemma710StoppedPrefixEndpoint start item.2).l -
                  old.cornerL : ℤ) : ℝ) ≤
                  verticalSourceThreshold - verticalTailThreshold) →
                ResidualBad full))
    (hhorizontal :
      ∀ full,
        EprimeHorizontalSourceEvent start horizontalCenter
          horizontalSourceThreshold full →
          ResidualBad full ∨
            ∃ item,
              EprimeFixedPSourceRunCandidate PrefixOK pointAt j sourceHeight
                firstBlock sourceSuffixes old q verticalGap start p full item ∧
                (¬ (|(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                    horizontalCenter| ≤
                    horizontalSourceThreshold - horizontalTailThreshold) →
                  ResidualBad full)) :
    EprimeFixedHorizonHeadroomSelector PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start horizontalCenter
      verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
      horizontalTailThreshold p ResidualBad
      (randomKVerticalFirstPassagePrefixFinset start verticalGap
        sourceSuffixes) :=
  eprimeFixedHorizonHeadroomSelector_of_routeCandidates
    (hprefixes :=
      randomKFixedSourceLedgerFamily_verticalFirstPassagePrefixFinset
        hstart hpoint_q hverticalGap hpoint_first hprefix_ok hmass)
    (hvertical := by
      intro full hsrc
      rcases hvertical full hsrc with hres | hcandidate
      · exact Or.inl hres
      · rcases hcandidate with
          ⟨item, hcandidate, hresidual_of_not_headroom⟩
        have hitem :
            item ∈
              randomKVerticalFirstPassagePrefixFinset start verticalGap
                sourceSuffixes :=
          eprimeFixedPSourceRunCandidate_mem_verticalFirstPassagePrefixFinset
            hcandidate
        exact
          Or.inr
            ⟨item, hitem, hcandidate, hresidual_of_not_headroom⟩)
    (hhorizontal := by
      intro full hsrc
      rcases hhorizontal full hsrc with hres | hcandidate
      · exact Or.inl hres
      · rcases hcandidate with
          ⟨item, hcandidate, hresidual_of_not_headroom⟩
        have hitem :
            item ∈
              randomKVerticalFirstPassagePrefixFinset start verticalGap
                sourceSuffixes :=
          eprimeFixedPSourceRunCandidate_mem_verticalFirstPassagePrefixFinset
            hcandidate
        exact
          Or.inr
            ⟨item, hitem, hcandidate, hresidual_of_not_headroom⟩)

/--
Build the fixed-source selector/headroom input from a candidate selector plus
residual guards for prefix-headroom failure.

This keeps the residual boundary on the source/prefix side: if the selected
prefix lacks headroom, the supplied guard must put the full event in
`ResidualBad`; otherwise the selected item is passed through with the
headroom proof.  The post-`k` tail event is not treated as residual here.
-/
theorem eprimeFixedSourceHeadroomSelector_of_candidate_or_residual
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (hprefixes :
      RandomKFixedSourceLedgerFamily PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start S)
    (hvertical :
      ∀ full, EprimeVerticalSourceEvent start old verticalSourceThreshold full →
        ResidualBad full ∨
          ∃ item, item ∈ S ∧
            full = taoSection7HoldIncrementsOfPrefixes sourceSuffixes ∧
              p = sourceSuffixes.length - item.1 ∧
                (¬ ((((lemma710StoppedPrefixEndpoint start item.2).l -
                    old.cornerL : ℤ) : ℝ) ≤
                    verticalSourceThreshold - verticalTailThreshold) →
                  ResidualBad full))
    (hhorizontal :
      ∀ full,
        EprimeHorizontalSourceEvent start horizontalCenter
          horizontalSourceThreshold full →
          ResidualBad full ∨
            ∃ item, item ∈ S ∧
              full = taoSection7HoldIncrementsOfPrefixes sourceSuffixes ∧
                p = sourceSuffixes.length - item.1 ∧
                  (¬ (|(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
                      horizontalCenter| ≤
                      horizontalSourceThreshold - horizontalTailThreshold) →
                    ResidualBad full)) :
    EprimeFixedSourceHeadroomSelector PrefixOK pointAt j sourceHeight
      firstBlock sourceSuffixes old q verticalGap start horizontalCenter
      verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
      horizontalTailThreshold p ResidualBad S where
  prefixes := hprefixes
  vertical_selected := by
    classical
    intro full hsrc
    rcases hvertical full hsrc with hres | hcandidate
    · exact Or.inl hres
    · rcases hcandidate with ⟨item, hitem, hfull, hp, hresidual_of_not_headroom⟩
      by_cases hheadroom :
          (((lemma710StoppedPrefixEndpoint start item.2).l -
            old.cornerL : ℤ) : ℝ) ≤
            verticalSourceThreshold - verticalTailThreshold
      · exact Or.inr ⟨item, hitem, hfull, hp, hheadroom⟩
      · exact Or.inl (hresidual_of_not_headroom hheadroom)
  horizontal_selected := by
    classical
    intro full hsrc
    rcases hhorizontal full hsrc with hres | hcandidate
    · exact Or.inl hres
    · rcases hcandidate with ⟨item, hitem, hfull, hp, hresidual_of_not_headroom⟩
      by_cases hheadroom :
          |(((lemma710StoppedPrefixEndpoint start item.2).j : ℕ) : ℝ) -
            horizontalCenter| ≤
            horizontalSourceThreshold - horizontalTailThreshold
      · exact Or.inr ⟨item, hitem, hfull, hp, hheadroom⟩
      · exact Or.inl (hresidual_of_not_headroom hheadroom)

theorem eprimeFixedSourceHeadroomSelector_to_fixedSourceSelectedSplit
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      EprimeFixedSourceHeadroomSelector PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start horizontalCenter
        verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
        horizontalTailThreshold p ResidualBad S) :
    EprimeFixedSourceSelectedSplit PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q verticalGap start horizontalCenter
      verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
      horizontalTailThreshold p ResidualBad S where
  prefixes := h.prefixes
  vertical_selected := by
    intro full hsrc
    rcases h.vertical_selected full hsrc with hres | hsel
    · exact Or.inl hres
    · rcases hsel with ⟨item, hitem, hfull, hp, hheadroom⟩
      rcases h.prefixes.ledger item hitem with ⟨first, hledger⟩
      rcases randomKSourceLedger_append_split_of_full_source hledger hfull hp with
        ⟨tail, hsplit, htail⟩
      exact Or.inr ⟨item, hitem, tail, hsplit, htail, hheadroom⟩
  horizontal_selected := by
    intro full hsrc
    rcases h.horizontal_selected full hsrc with hres | hsel
    · exact Or.inl hres
    · rcases hsel with ⟨item, hitem, hfull, hp, hheadroom⟩
      rcases h.prefixes.ledger item hitem with ⟨first, hledger⟩
      rcases randomKSourceLedger_append_split_of_full_source hledger hfull hp with
        ⟨tail, hsplit, htail⟩
      exact Or.inr ⟨item, hitem, tail, hsplit, htail, hheadroom⟩

theorem eprimeFixedHorizonHeadroomSelector_to_fixedSourceSelectedSplit
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      EprimeFixedHorizonHeadroomSelector PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start horizontalCenter
        verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
        horizontalTailThreshold p ResidualBad S) :
    EprimeFixedSourceSelectedSplit PrefixOK pointAt j sourceHeight firstBlock
      sourceSuffixes old q verticalGap start horizontalCenter
      verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
      horizontalTailThreshold p ResidualBad S where
  prefixes := h.prefixes
  vertical_selected := by
    intro full hsrc
    rcases h.vertical_selected full hsrc with hres | hsel
    · exact Or.inl hres
    · rcases hsel with ⟨item, hitem, hfull, hhorizon, hheadroom⟩
      rcases h.prefixes.ledger item hitem with ⟨first, hledger⟩
      rcases
        randomKSourceLedger_append_split_of_source_take_horizon hledger
          hhorizon hfull with
        ⟨tail, hsplit, htail⟩
      exact Or.inr ⟨item, hitem, tail, hsplit, htail, hheadroom⟩
  horizontal_selected := by
    intro full hsrc
    rcases h.horizontal_selected full hsrc with hres | hsel
    · exact Or.inl hres
    · rcases hsel with ⟨item, hitem, hfull, hhorizon, hheadroom⟩
      rcases h.prefixes.ledger item hitem with ⟨first, hledger⟩
      rcases
        randomKSourceLedger_append_split_of_source_take_horizon hledger
          hhorizon hfull with
        ⟨tail, hsplit, htail⟩
      exact Or.inr ⟨item, hitem, tail, hsplit, htail, hheadroom⟩

theorem eprimeFixedSourceSelectedSplit_to_eprimeSelectedSourceSplit
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {sourceHeight : ℕ} {firstBlock : List ℕ}
    {sourceSuffixes : List (List ℕ)}
    {old : TaoSection7Triangle} {q verticalGap : ℕ}
    {start : TaoSection7RenewalPoint}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      EprimeFixedSourceSelectedSplit PrefixOK pointAt j sourceHeight
        firstBlock sourceSuffixes old q verticalGap start horizontalCenter
        verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
        horizontalTailThreshold p ResidualBad S) :
    EprimeSelectedSourceSplit PrefixOK start old horizontalCenter
      verticalSourceThreshold verticalTailThreshold horizontalSourceThreshold
      horizontalTailThreshold p ResidualBad S where
  prefixes :=
    randomKFixedSourceLedgerFamily_to_randomKSourceLedgerFamily h.prefixes
  vertical_selected := h.vertical_selected
  horizontal_selected := h.horizontal_selected

theorem eprimeSelectedSourceSplit_to_verticalSourceCoverage
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      EprimeSelectedSourceSplit PrefixOK start old horizontalCenter
        verticalSourceThreshold verticalTailThreshold
        horizontalSourceThreshold horizontalTailThreshold p ResidualBad S) :
    EprimeVerticalSourceCoverage PrefixOK start old verticalSourceThreshold
      verticalTailThreshold p ResidualBad S :=
  eprimeVerticalSourceCoverage_of_selectedSplit h.prefixes h.vertical_selected

theorem eprimeSelectedSourceSplit_to_horizontalSourceCoverage
    {PrefixOK : ℕ × List TaoSection7RenewalPoint → Prop}
    {start : TaoSection7RenewalPoint} {old : TaoSection7Triangle}
    {horizontalCenter verticalSourceThreshold verticalTailThreshold
      horizontalSourceThreshold horizontalTailThreshold : ℝ}
    {p : ℕ}
    {ResidualBad : List TaoSection7RenewalPoint → Prop}
    {S : Finset (ℕ × List TaoSection7RenewalPoint)}
    (h :
      EprimeSelectedSourceSplit PrefixOK start old horizontalCenter
        verticalSourceThreshold verticalTailThreshold
        horizontalSourceThreshold horizontalTailThreshold p ResidualBad S) :
    EprimeHorizontalSourceCoverage PrefixOK start horizontalCenter
      horizontalSourceThreshold horizontalTailThreshold p ResidualBad S :=
  eprimeHorizontalSourceCoverage_of_selectedSplit h.prefixes h.horizontal_selected

end TaoSection7Lemma710

end

end Tao
end Erdos1135SecondScale
