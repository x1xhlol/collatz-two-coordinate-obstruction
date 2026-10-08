import Erdos1135.Tao.Renewal.PathGrowth
import Mathlib.Tactic

/-!
# Section 7 Source Path Data Interface

This module records the bundled data interface needed to feed the checked
`PathGrowth` later-black consumer in the Proposition 7.8 Case 3 route.

It is only an interface layer.  It does not prove that a suffix is the actual
post-pivot source suffix, does not construct the source path from Tao's source
decomposition, and does not prove source `(7.11)`, q-room, first-stopping,
Lemma 7.9, Lemma 7.10, Tao's many-whites inequality, `(7.41)`, Proposition
7.8, or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

/--
Bundled source-path data needed by the `PathGrowth` later-black consumer.

The hard future theorem is the producer that fills this structure from Tao's
actual source decomposition after the Case 3 pivot.
-/
structure TaoSection7Case3SourcePathData
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    (n J A : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P threshold q : ℕ)
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ)) : Prop where
  coverage : taoSection7SourceSuffixCoversWindow q P pres
  point_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint
  point_candidate :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      pointAt candidate =
        (taoSection7SourceHitPathPoint j s pre pres
          (candidate - q)).toPoint
  white_iff :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      (W candidate ↔
        taoSection7SourceWhitePoint n xi epsilon (pointAt candidate))
  domain :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      taoSection7SourcePointInDomain J (pointAt candidate)

/--
Once a real source-path producer supplies `TaoSection7Case3SourcePathData`,
the current `PathGrowth` later-black assembly theorem applies directly.
-/
theorem taoSection7Case3_exists_laterBlackPivotStep_of_sourcePathData
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hdata :
      TaoSection7Case3SourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hmem_old : old.Mem (pointAt q))
    (hsize : old.size < taoSection7Case3LargeTriangleBound A q)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) ∧
        ¬ W candidate ∧
          taoSection7Case3HeightExitBound
            (taoSection7Case3ExitGapBound A) q < candidate ∧
            candidate < P ∧ candidate - q ≤ pres.length ∧
              ∃ Γ : TaoSection7Triangle,
                taoSection7Case3BlackPivotStep
                  (taoSection7SourceBlackInDomain n xi epsilon J)
                  family pointAt old Γ candidate := by
  exact
    taoSection7Case3_exists_laterBlackPivotStep_of_searchRoom_sourceHitPath
      (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
      (xi := xi) (epsilon := epsilon) (family := family) (old := old)
      (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
      (pre := pre) (pres := pres)
      hlow hroom hdata.coverage hdata.point_q hdata.point_candidate
      hmem_old hsize hdata.white_iff hdata.domain hcover

/--
Generic-gap source-path data for the base-aware Case 3 recurrence route.

This is the `SourcePathData` analogue for an arbitrary calibrated `gapBound`;
the source proof must still produce the endpoint identifications and domain
facts for the actual restarted source suffix.
-/
structure TaoSection7Case3SourcePathDataWithGap
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    (n J : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P threshold q : ℕ) (gapBound : ℕ → ℕ)
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ)) : Prop where
  coverage : taoSection7SourceSuffixCoversWindow q P pres
  point_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint
  point_candidate :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) →
      pointAt candidate =
        (taoSection7SourceHitPathPoint j s pre pres
          (candidate - q)).toPoint
  white_iff :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) →
      (W candidate ↔
        taoSection7SourceWhitePoint n xi epsilon (pointAt candidate))
  domain :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) →
      taoSection7SourcePointInDomain J (pointAt candidate)

theorem taoSection7Case3_exists_laterBlackPivotStep_of_sourcePathData_scale
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hdata :
      TaoSection7Case3SourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hmem_old : old.Mem (pointAt q))
    (hsize : old.size < bound q)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) ∧
        ¬ W candidate ∧
          taoSection7Case3HeightExitBound gapBound q < candidate ∧
            candidate < P ∧ candidate - q ≤ pres.length ∧
              ∃ Γ : TaoSection7Triangle,
                taoSection7Case3BlackPivotStep
                  (taoSection7SourceBlackInDomain n xi epsilon J)
                  family pointAt old Γ candidate := by
  exact
    taoSection7Case3_exists_laterBlackPivotStep_of_searchRoom_sourceHitPath_scale
      (W := W) (pointAt := pointAt) (n := n) (J := J)
      (xi := xi) (epsilon := epsilon) (family := family) (old := old)
      (bound := bound) (gapBound := gapBound) (P := P)
      (threshold := threshold) (q := q) (j := j) (s := s)
      (pre := pre) (pres := pres)
      hscale hlow hroom hdata.coverage hdata.point_q hdata.point_candidate
      hmem_old hsize hdata.white_iff hdata.domain hcover

/--
More concrete local provenance for `TaoSection7Case3SourcePathData`.

The hard future source theorem should prove this from the actual source
decomposition.  This package removes duplicate endpoint fields by asking for a
single block-scoped source-path model on `{q} ∪ laterSearchIcc`.
-/
structure TaoSection7Case3SourceSuffixProvenance
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    (n J A : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P threshold q : ℕ)
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ)) : Prop where
  coverage : taoSection7SourceSuffixCoversWindow q P pres
  pointAt_source :
    ∀ t : ℕ,
      t ∈
          insert q
            (Finset.Icc
              (taoSection7Case3LaterSearchStart
                (taoSection7Case3ExitGapBound A) q)
              (taoSection7Case3LaterSearchStart
                (taoSection7Case3ExitGapBound A) q + threshold)) →
      pointAt t =
        (taoSection7SourceHitPathPoint j s pre pres (t - q)).toPoint
  white_iff_source :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      (W candidate ↔
        taoSection7SourceWhitePoint n xi epsilon
          (taoSection7SourceHitPathPoint j s pre pres
            (candidate - q)).toPoint)
  domain_source :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      taoSection7SourcePointInDomain J
        (taoSection7SourceHitPathPoint j s pre pres
          (candidate - q)).toPoint

/-- Starting source index after the finite source blocks before the pivot. -/
def taoSection7SourceBlockStartJ (before : List (List ℕ)) : ℕ+ :=
  ⟨1 + (taoSection7SourceBlocks before).length, by omega⟩

/-- Starting vertical coordinate after the finite source blocks before the pivot. -/
def taoSection7SourceBlockStartS (before : List (List ℕ)) : ℕ :=
  (taoSection7SourceBlocks before).sum

/-- Starting source index after `before`, relative to an arbitrary source index. -/
def taoSection7SourceBlockStartJFrom
    (j : ℕ+) (before : List (List ℕ)) : ℕ+ :=
  taoSection7ShiftIndex j (taoSection7SourceBlocks before).length

/-- Starting vertical coordinate after `before`, relative to an arbitrary height. -/
def taoSection7SourceBlockStartSFrom
    (s : ℕ) (before : List (List ℕ)) : ℕ :=
  s + (taoSection7SourceBlocks before).sum

theorem taoSection7ShiftIndex_assoc
    (j : ℕ+) (a b : ℕ) :
    taoSection7ShiftIndex (taoSection7ShiftIndex j a) b =
      taoSection7ShiftIndex j (a + b) := by
  apply Subtype.ext
  simp [taoSection7ShiftIndex]
  omega

@[simp] theorem taoSection7SourceBlocks_append
    (xs ys : List (List ℕ)) :
    taoSection7SourceBlocks (xs ++ ys) =
      taoSection7SourceBlocks xs ++ taoSection7SourceBlocks ys := by
  induction xs with
  | nil =>
      simp [taoSection7SourceBlocks]
  | cons x xs ih =>
      simp [taoSection7SourceBlocks, ih, List.append_assoc]

@[simp] theorem taoSection7SourceBlocks_append_length
    (xs ys : List (List ℕ)) :
    (taoSection7SourceBlocks (xs ++ ys)).length =
      (taoSection7SourceBlocks xs).length +
        (taoSection7SourceBlocks ys).length := by
  simp [taoSection7SourceBlocks_append]

@[simp] theorem taoSection7SourceBlocks_append_sum
    (xs ys : List (List ℕ)) :
    (taoSection7SourceBlocks (xs ++ ys)).sum =
      (taoSection7SourceBlocks xs).sum +
        (taoSection7SourceBlocks ys).sum := by
  simp [taoSection7SourceBlocks_append, List.sum_append]

/--
Distinguished-first convention for source-prefix endpoint algebra: after
consuming `before.length + 1` source-hit blocks from an initial block `first`,
the source-hit path reaches the next block `pre` at the accumulated coordinates.
Future producer statements must align this convention with the same `q` used by
the source-suffix coverage gate.
-/
theorem taoSection7SourceHitPathPoint_after_prefix
    (j : ℕ+) (s : ℕ)
    (first : List ℕ) (before : List (List ℕ))
    (pre : List ℕ) (pres : List (List ℕ)) :
    taoSection7SourceHitPathPoint j s first
        (before ++ pre :: pres) (before.length + 1) =
      taoSection7SourceHitPoint
        (taoSection7SourceBlockStartJFrom j (first :: before))
        (taoSection7SourceBlockStartSFrom s (first :: before)) pre := by
  induction before generalizing j s first with
  | nil =>
      simp only [List.nil_append, List.length_nil, zero_add]
      rw [taoSection7SourceHitPathPoint_cons_succ]
      simp [taoSection7SourceBlockStartJFrom,
        taoSection7SourceBlockStartSFrom, taoSection7SourceBlocks,
        Nat.add_assoc]
  | cons next rest ih =>
      have h :=
        ih (taoSection7ShiftIndex j (first.length + 1))
          (s + first.sum + 3) next
      simpa [taoSection7SourceBlockStartJFrom,
        taoSection7SourceBlockStartSFrom, taoSection7SourceBlocks,
        taoSection7ShiftIndex_assoc,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/--
After the same prefix, continuing `n` further source-hit steps agrees with
starting the source-hit path from the accumulated coordinates at the next block.
-/
theorem taoSection7SourceHitPathPoint_after_prefix_add
    (j : ℕ+) (s : ℕ)
    (first : List ℕ) (before : List (List ℕ))
    (pre : List ℕ) (pres : List (List ℕ)) (n : ℕ) :
    taoSection7SourceHitPathPoint j s first
        (before ++ pre :: pres) (before.length + n + 1) =
      taoSection7SourceHitPathPoint
        (taoSection7SourceBlockStartJFrom j (first :: before))
        (taoSection7SourceBlockStartSFrom s (first :: before))
        pre pres n := by
  induction before generalizing j s first with
  | nil =>
      simp only [List.nil_append, List.length_nil, zero_add]
      rw [taoSection7SourceHitPathPoint_cons_succ]
      simp [taoSection7SourceBlockStartJFrom,
        taoSection7SourceBlockStartSFrom, taoSection7SourceBlocks,
        Nat.add_assoc]
  | cons next rest ih =>
      have h :=
        ih (taoSection7ShiftIndex j (first.length + 1))
          (s + first.sum + 3) next
      simp only [List.cons_append, List.length_cons]
      rw [show rest.length + 1 + n + 1 = (rest.length + n + 1) + 1 by
        omega]
      rw [taoSection7SourceHitPathPoint_cons_succ
        (j := j) (s := s) (pre := first) (next := next)
        (rest := rest ++ pre :: pres) (n := rest.length + n + 1)]
      simpa [taoSection7SourceBlockStartJFrom,
        taoSection7SourceBlockStartSFrom, taoSection7SourceBlocks,
        taoSection7ShiftIndex_assoc,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/--
If a global source block list splits as `before ++ pre :: pres`, and the source
window only asks for hit offsets below `P <= blocks.length`, then the suffix
`pres` covers the `P` window from the pivot hit `q = before.length`.
-/
theorem taoSection7SourceSuffixCoversWindow_of_blockSplit
    {blocks before : List (List ℕ)} {pre : List ℕ} {pres : List (List ℕ)}
    {q P : ℕ}
    (hblocks : blocks = before ++ pre :: pres)
    (hq : q = before.length)
    (hP : P ≤ blocks.length) :
    taoSection7SourceSuffixCoversWindow q P pres := by
  subst blocks
  subst q
  simpa [taoSection7SourceSuffixCoversWindow] using hP

/--
A block-scoped source-suffix provenance package supplies the exact
`TaoSection7Case3SourcePathData` fields expected by the current `PathGrowth`
consumer.
-/
theorem taoSection7Case3SourcePathData_of_sourceSuffixProvenance
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hprov :
      TaoSection7Case3SourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q j s pre pres) :
    TaoSection7Case3SourcePathData
      W pointAt n J A xi epsilon P threshold q j s pre pres := by
  refine
    { coverage := hprov.coverage
      point_q := ?_
      point_candidate := ?_
      white_iff := ?_
      domain := ?_ }
  · have hq_mem :
        q ∈
          insert q
            (Finset.Icc
              (taoSection7Case3LaterSearchStart
                (taoSection7Case3ExitGapBound A) q)
              (taoSection7Case3LaterSearchStart
                (taoSection7Case3ExitGapBound A) q + threshold)) := by
      simp
    simpa using hprov.pointAt_source q hq_mem
  · intro candidate hcandidate
    exact hprov.pointAt_source candidate (by simp [hcandidate])
  · intro candidate hcandidate
    have hpoint := hprov.pointAt_source candidate (by simp [hcandidate])
    simpa [hpoint] using hprov.white_iff_source candidate hcandidate
  · intro candidate hcandidate
    have hpoint := hprov.pointAt_source candidate (by simp [hcandidate])
    simpa [hpoint] using hprov.domain_source candidate hcandidate

/--
Distinguished-first form of source-suffix coverage.

This is the global split coverage helper with the prefix instantiated as
`first :: before`, so the pivot source-hit index is `before.length + 1`.
-/
theorem taoSection7SourceSuffixCoversWindow_of_distinguishedBlockSplit
    {blocks : List (List ℕ)} {first : List ℕ} {before : List (List ℕ)}
    {pre : List ℕ} {pres : List (List ℕ)}
    {q P : ℕ}
    (hblocks : blocks = first :: before ++ pre :: pres)
    (hq : q = before.length + 1)
    (hP : P ≤ blocks.length) :
    taoSection7SourceSuffixCoversWindow q P pres := by
  exact
    taoSection7SourceSuffixCoversWindow_of_blockSplit
      (blocks := blocks) (before := first :: before) (pre := pre)
      (pres := pres) hblocks (by simp [hq]) hP

/--
Producer-facing provenance for the Case 3 source suffix in the global-prefix
convention `blocks = before ++ pre :: pres`.

This pins the local source-suffix interface to a global split and records
no-`3` provenance.  It still does not prove that the split is Tao's actual
source decomposition.
-/
structure TaoSection7Case3GlobalSourceSuffixProvenance
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    (n J A : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P threshold q : ℕ)
    (blocks before : List (List ℕ)) (pre : List ℕ)
    (pres : List (List ℕ)) : Prop where
  blocks_eq : blocks = before ++ pre :: pres
  q_eq : q = before.length
  window_le : P ≤ blocks.length
  noThree_before : ∀ block ∈ before, taoSection7NoThree block
  noThree_pre : taoSection7NoThree pre
  noThree_pres : ∀ block ∈ pres, taoSection7NoThree block
  pointAt_source :
    ∀ t : ℕ,
      t ∈
          insert q
            (Finset.Icc
              (taoSection7Case3LaterSearchStart
                (taoSection7Case3ExitGapBound A) q)
              (taoSection7Case3LaterSearchStart
                (taoSection7Case3ExitGapBound A) q + threshold)) →
      pointAt t =
        (taoSection7SourceHitPathPoint
          (taoSection7SourceBlockStartJ before)
          (taoSection7SourceBlockStartS before)
          pre pres (t - q)).toPoint
  white_iff_source :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      (W candidate ↔
        taoSection7SourceWhitePoint n xi epsilon
          (taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ before)
            (taoSection7SourceBlockStartS before)
            pre pres (candidate - q)).toPoint)
  domain_source :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      taoSection7SourcePointInDomain J
        (taoSection7SourceHitPathPoint
          (taoSection7SourceBlockStartJ before)
          (taoSection7SourceBlockStartS before)
          pre pres (candidate - q)).toPoint

/--
The global-prefix wrapper specializes the committed local source-suffix
provenance interface at the coordinates accumulated by `before`.
-/
theorem TaoSection7Case3GlobalSourceSuffixProvenance.to_sourceSuffixProvenance
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hglobal :
      TaoSection7Case3GlobalSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q blocks before pre pres) :
    TaoSection7Case3SourceSuffixProvenance
      W pointAt n J A xi epsilon P threshold q
      (taoSection7SourceBlockStartJ before)
      (taoSection7SourceBlockStartS before) pre pres := by
  refine
    { coverage := ?_
      pointAt_source := hglobal.pointAt_source
      white_iff_source := hglobal.white_iff_source
      domain_source := hglobal.domain_source }
  exact
    taoSection7SourceSuffixCoversWindow_of_blockSplit
      hglobal.blocks_eq hglobal.q_eq hglobal.window_le

/--
Consumer-facing projection from the global-prefix provenance wrapper.
-/
theorem TaoSection7Case3GlobalSourceSuffixProvenance.to_sourcePathData
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hglobal :
      TaoSection7Case3GlobalSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q blocks before pre pres) :
    TaoSection7Case3SourcePathData
      W pointAt n J A xi epsilon P threshold q
      (taoSection7SourceBlockStartJ before)
      (taoSection7SourceBlockStartS before) pre pres :=
  taoSection7Case3SourcePathData_of_sourceSuffixProvenance
    hglobal.to_sourceSuffixProvenance

/--
Producer-facing provenance for the distinguished-first convention
`blocks = first :: before ++ pre :: pres`.

This records the same source split used by the all-offset endpoint algebra,
where the pivot block has source-hit index `before.length + 1`.
-/
structure TaoSection7Case3DistinguishedSourceSuffixProvenance
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    (n J A : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P threshold q : ℕ)
    (blocks : List (List ℕ)) (first : List ℕ)
    (before : List (List ℕ)) (pre : List ℕ)
    (pres : List (List ℕ)) : Prop where
  blocks_eq : blocks = first :: before ++ pre :: pres
  q_eq : q = before.length + 1
  window_le : P ≤ blocks.length
  noThree_first : taoSection7NoThree first
  noThree_before : ∀ block ∈ before, taoSection7NoThree block
  noThree_pre : taoSection7NoThree pre
  noThree_pres : ∀ block ∈ pres, taoSection7NoThree block
  pointAt_source :
    ∀ t : ℕ,
      t ∈
          insert q
            (Finset.Icc
              (taoSection7Case3LaterSearchStart
                (taoSection7Case3ExitGapBound A) q)
              (taoSection7Case3LaterSearchStart
                (taoSection7Case3ExitGapBound A) q + threshold)) →
      pointAt t =
        (taoSection7SourceHitPathPoint
          (taoSection7SourceBlockStartJ (first :: before))
          (taoSection7SourceBlockStartS (first :: before))
          pre pres (t - q)).toPoint
  white_iff_source :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      (W candidate ↔
        taoSection7SourceWhitePoint n xi epsilon
          (taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ (first :: before))
            (taoSection7SourceBlockStartS (first :: before))
            pre pres (candidate - q)).toPoint)
  domain_source :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      taoSection7SourcePointInDomain J
        (taoSection7SourceHitPathPoint
          (taoSection7SourceBlockStartJ (first :: before))
          (taoSection7SourceBlockStartS (first :: before))
          pre pres (candidate - q)).toPoint

/--
The distinguished-first wrapper specializes the committed local source-suffix
provenance interface at the coordinates accumulated by `first :: before`.
-/
theorem TaoSection7Case3DistinguishedSourceSuffixProvenance.to_sourceSuffixProvenance
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {first : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hsrc :
      TaoSection7Case3DistinguishedSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q
        blocks first before pre pres) :
    TaoSection7Case3SourceSuffixProvenance
      W pointAt n J A xi epsilon P threshold q
      (taoSection7SourceBlockStartJ (first :: before))
      (taoSection7SourceBlockStartS (first :: before)) pre pres := by
  refine
    { coverage := ?_
      pointAt_source := hsrc.pointAt_source
      white_iff_source := hsrc.white_iff_source
      domain_source := hsrc.domain_source }
  exact
    taoSection7SourceSuffixCoversWindow_of_distinguishedBlockSplit
      hsrc.blocks_eq hsrc.q_eq hsrc.window_le

/--
Consumer-facing projection from the distinguished-first provenance wrapper.
-/
theorem TaoSection7Case3DistinguishedSourceSuffixProvenance.to_sourcePathData
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {first : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hsrc :
      TaoSection7Case3DistinguishedSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q
        blocks first before pre pres) :
    TaoSection7Case3SourcePathData
      W pointAt n J A xi epsilon P threshold q
      (taoSection7SourceBlockStartJ (first :: before))
      (taoSection7SourceBlockStartS (first :: before)) pre pres :=
  taoSection7Case3SourcePathData_of_sourceSuffixProvenance
    hsrc.to_sourceSuffixProvenance

end Tao
end Erdos1135
