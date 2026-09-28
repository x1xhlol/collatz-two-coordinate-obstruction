import Erdos1135.Tao.Renewal.Prop78Case3TriangleExit
import Erdos1135.Tao.Renewal.GeometryBridge
import Erdos1135.Tao.Renewal.VerticalFirstPassageBasic
import Mathlib.Tactic

/-!
# Section 7 Renewal Path Growth Support

This module records deterministic renewal/source-hit path support for the
Proposition 7.8 Case 3 route.  It proves that finite Hold-increment paths grow
in the `l` coordinate, rewrites those paths as recursively described source-hit
paths, and packages the explicit finite suffix-length gate needed before the
source-hit path can be used in Case 3.

It is support-only.  It does not prove the actual source `(7.11)` bridge, does
not identify the abstract Case 3 `pointAt` function with an actual source path,
does not prove source-suffix coverage, q-room, later-black search, first
stopping/new-triangle compatibility, Lemma 7.9, Lemma 7.10, Tao's
many-whites inequality, `(7.41)`, Proposition 7.8, or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

theorem taoSection7RenewalPathPoint_sourcePrefixes_drop_add
    (p : TaoSection7RenewalPoint) (pres : List (List ℕ)) (q n : ℕ) :
    taoSection7RenewalPathPoint
        (taoSection7RenewalPathPoint p
          (taoSection7HoldIncrementsOfPrefixes pres) q)
        (taoSection7HoldIncrementsOfPrefixes (pres.drop q)) n =
      taoSection7RenewalPathPoint p
        (taoSection7HoldIncrementsOfPrefixes pres) (q + n) := by
  simpa [taoSection7HoldIncrementsOfPrefixes] using
    taoSection7RenewalPathPoint_drop_add p
      (taoSection7HoldIncrementsOfPrefixes pres) q n

theorem taoSection7RenewalPathPoint_sourcePrefixes_drop_candidate_sub
    {p : TaoSection7RenewalPoint} {pres : List (List ℕ)}
    {q candidate : ℕ}
    (hq : q ≤ candidate) :
    taoSection7RenewalPathPoint
        (taoSection7RenewalPathPoint p
          (taoSection7HoldIncrementsOfPrefixes pres) q)
        (taoSection7HoldIncrementsOfPrefixes (pres.drop q))
        (candidate - q) =
      taoSection7RenewalPathPoint p
        (taoSection7HoldIncrementsOfPrefixes pres) candidate := by
  have h :=
    taoSection7RenewalPathPoint_sourcePrefixes_drop_add
      p pres q (candidate - q)
  have hsum : q + (candidate - q) = candidate := Nat.add_sub_of_le hq
  simpa [hsum] using h

theorem taoSection7HoldIncrementOfPrefix_l_ge_one
    (pre : List ℕ) :
    (1 : ℤ) ≤ (taoSection7HoldIncrementOfPrefix pre).l := by
  induction pre with
  | nil =>
      simp [taoSection7HoldIncrementOfPrefix]
  | cons a pre ih =>
      simp [taoSection7HoldIncrementOfPrefix] at ih ⊢
      omega

theorem taoSection7HoldIncrementsOfPrefixes_all_l_ge_one
    (pres : List (List ℕ)) :
    taoSection7AllHoldIncrementsLGeOne
      (taoSection7HoldIncrementsOfPrefixes pres) := by
  intro h hh
  rw [taoSection7HoldIncrementsOfPrefixes] at hh
  rcases List.mem_map.mp hh with ⟨pre, _hpre, rfl⟩
  exact taoSection7HoldIncrementOfPrefix_l_ge_one pre

theorem taoSection7HoldIncrementsOfPrefixes_l_ge_one
    {pres : List (List ℕ)} {h : TaoSection7RenewalPoint}
    (hh : h ∈ taoSection7HoldIncrementsOfPrefixes pres) :
    (1 : ℤ) ≤ h.l :=
  taoSection7HoldIncrementsOfPrefixes_all_l_ge_one pres h hh

theorem taoSection7HoldIncrementsOfPrefixes_raise_l
    {pres : List (List ℕ)} {h : TaoSection7RenewalPoint}
    (hh : h ∈ taoSection7HoldIncrementsOfPrefixes pres)
    (p : TaoSection7RenewalPoint) :
    p.l + 1 ≤ (p + h).l := by
  have hh_l : (1 : ℤ) ≤ h.l :=
    taoSection7HoldIncrementsOfPrefixes_l_ge_one hh
  simp
  omega

theorem taoSection7RenewalPathPoint_l_sub_growth_ge_steps
    {p : TaoSection7RenewalPoint} {holds : List TaoSection7RenewalPoint}
    {n : ℕ}
    (hn : n ≤ holds.length)
    (hall : taoSection7AllHoldIncrementsLGeOne holds) :
    (n : ℤ) ≤
      (taoSection7RenewalPathPoint p holds n).l - p.l := by
  have hgrowth :
      p.l + (n : ℤ) ≤
        (taoSection7RenewalPathPoint p holds n).l :=
    taoSection7RenewalPathPoint_l_growth_ge_steps p holds n hn hall
  omega

theorem taoSection7Case3_sourceVerticalGrowth_of_path_steps
    {p : TaoSection7RenewalPoint} {holds : List TaoSection7RenewalPoint}
    {A pivot n : ℕ}
    (hn : n ≤ holds.length)
    (hall : taoSection7AllHoldIncrementsLGeOne holds)
    (hsteps : taoSection7Case3SufficientVerticalSteps A pivot n) :
    taoSection7Case3LargeTriangleBound A pivot ≤
      ((((taoSection7RenewalPathPoint p holds n).toPoint.l -
        p.toPoint.l : ℤ) : ℝ) * Real.log 2) := by
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hgrowth_int :
      (n : ℤ) ≤
        (taoSection7RenewalPathPoint p holds n).l - p.l :=
    taoSection7RenewalPathPoint_l_sub_growth_ge_steps hn hall
  have hgrowth_real :
      (n : ℝ) ≤
        (((taoSection7RenewalPathPoint p holds n).l - p.l : ℤ) : ℝ) := by
    exact_mod_cast hgrowth_int
  have hmul :
      (n : ℝ) * Real.log 2 ≤
        (((taoSection7RenewalPathPoint p holds n).l - p.l : ℤ) : ℝ) *
          Real.log 2 :=
    mul_le_mul_of_nonneg_right hgrowth_real hlog2_nonneg
  exact hsteps.trans (by
    simpa [TaoSection7RenewalPoint.toPoint] using hmul)

/--
Generic scale-compatible vertical-growth bridge.  The Case 3 source-pivot
route can instantiate `bound/gapBound` with the printed base-4 pair or with a
base-repaired `Kcut` pair.
-/
theorem taoSection7Case3_sourceVerticalGrowth_of_scale_path
    {p : TaoSection7RenewalPoint} {holds : List TaoSection7RenewalPoint}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {q candidate : ℕ}
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hcandidate :
      taoSection7Case3HeightExitBound gapBound q < candidate)
    (hlen : candidate - q ≤ holds.length)
    (hall : taoSection7AllHoldIncrementsLGeOne holds) :
    bound q ≤
      ((((taoSection7RenewalPathPoint p holds (candidate - q)).toPoint.l -
        p.toPoint.l : ℤ) : ℝ) * Real.log 2) := by
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hgap_le_steps : gapBound q ≤ candidate - q := by
    dsimp [taoSection7Case3HeightExitBound] at hcandidate
    omega
  have hgrowth_int :
      ((candidate - q : ℕ) : ℤ) ≤
        (taoSection7RenewalPathPoint p holds (candidate - q)).l - p.l :=
    taoSection7RenewalPathPoint_l_sub_growth_ge_steps hlen hall
  have hgap_growth_int :
      ((gapBound q : ℕ) : ℤ) ≤
        (taoSection7RenewalPathPoint p holds (candidate - q)).l - p.l :=
    le_trans (by exact_mod_cast hgap_le_steps) hgrowth_int
  have hgap_growth_real :
      (gapBound q : ℝ) ≤
        (((taoSection7RenewalPathPoint p holds (candidate - q)).l -
          p.l : ℤ) : ℝ) := by
    exact_mod_cast hgap_growth_int
  exact (hscale.sufficient q).trans (by
    simpa [TaoSection7RenewalPoint.toPoint] using
      mul_le_mul_of_nonneg_right hgap_growth_real hlog2_nonneg)

/--
Concrete-height-exit bridge: once the candidate is strictly past Tao's
`10 * 4^A(1+q)^3` gap and the finite renewal path contains the corresponding
number of increments, the endpoint path point satisfies the Case 3 real
vertical-growth premise.
-/
theorem taoSection7Case3_sourceVerticalGrowth_of_concreteHeightExit_path
    {p : TaoSection7RenewalPoint} {holds : List TaoSection7RenewalPoint}
    {A q candidate : ℕ}
    (hcandidate :
      taoSection7Case3HeightExitBound
        (taoSection7Case3ExitGapBound A) q < candidate)
    (hlen : candidate - q ≤ holds.length)
    (hall : taoSection7AllHoldIncrementsLGeOne holds) :
    taoSection7Case3LargeTriangleBound A q ≤
      ((((taoSection7RenewalPathPoint p holds (candidate - q)).toPoint.l -
        p.toPoint.l : ℤ) : ℝ) * Real.log 2) :=
  taoSection7Case3_sourceVerticalGrowth_of_path_steps
    hlen hall
    (taoSection7Case3_sufficientVerticalSteps_of_concreteHeightExit
      hcandidate)

/--
Source-list specialization: for the finite list of Hold increments associated
to no-`3` source prefixes, the `l >= 1` increment hypothesis is automatic.  The
remaining `hlen` hypothesis is the explicit `candidate - q <= pres.length`
path-index gate.
-/
theorem taoSection7Case3_sourceVerticalGrowth_of_concreteHeightExit_sourcePrefixes
    {p : TaoSection7RenewalPoint} {pres : List (List ℕ)}
    {A q candidate : ℕ}
    (hcandidate :
      taoSection7Case3HeightExitBound
        (taoSection7Case3ExitGapBound A) q < candidate)
    (hlen : candidate - q ≤ pres.length) :
    taoSection7Case3LargeTriangleBound A q ≤
      ((((taoSection7RenewalPathPoint p
          (taoSection7HoldIncrementsOfPrefixes pres) (candidate - q)).toPoint.l -
        p.toPoint.l : ℤ) : ℝ) * Real.log 2) := by
  have hlen_holds :
      candidate - q ≤ (taoSection7HoldIncrementsOfPrefixes pres).length := by
    simpa [taoSection7HoldIncrementsOfPrefixes] using hlen
  exact
    taoSection7Case3_sourceVerticalGrowth_of_concreteHeightExit_path
      hcandidate hlen_holds
      (taoSection7HoldIncrementsOfPrefixes_all_l_ge_one pres)

theorem taoSection7Case3_sourceVerticalGrowth_of_scale_sourcePrefixes
    {p : TaoSection7RenewalPoint} {pres : List (List ℕ)}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {q candidate : ℕ}
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hcandidate :
      taoSection7Case3HeightExitBound gapBound q < candidate)
    (hlen : candidate - q ≤ pres.length) :
    bound q ≤
      ((((taoSection7RenewalPathPoint p
          (taoSection7HoldIncrementsOfPrefixes pres) (candidate - q)).toPoint.l -
        p.toPoint.l : ℤ) : ℝ) * Real.log 2) := by
  have hlen_holds :
      candidate - q ≤ (taoSection7HoldIncrementsOfPrefixes pres).length := by
    simpa [taoSection7HoldIncrementsOfPrefixes] using hlen
  exact
    taoSection7Case3_sourceVerticalGrowth_of_scale_path
      hscale hcandidate hlen_holds
      (taoSection7HoldIncrementsOfPrefixes_all_l_ge_one pres)

/--
Recursive source-hit point after consuming `n` following no-`3` prefixes.
This mirrors the source-list decomposition and clamps once the finite prefix
list is exhausted.
-/
def taoSection7SourceHitPathPoint
    (j : ℕ+) (s : ℕ) (pre : List ℕ) : List (List ℕ) → ℕ →
      TaoSection7RenewalPoint
  | _pres, 0 => taoSection7SourceHitPoint j s pre
  | [], _n + 1 => taoSection7SourceHitPoint j s pre
  | next :: rest, n + 1 =>
      taoSection7SourceHitPathPoint
        (taoSection7ShiftIndex j (pre.length + 1))
        (s + pre.sum + 3) next rest n

@[simp] theorem taoSection7SourceHitPathPoint_zero
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ)) :
    taoSection7SourceHitPathPoint j s pre pres 0 =
      taoSection7SourceHitPoint j s pre := by
  cases pres <;> rfl

@[simp] theorem taoSection7SourceHitPathPoint_nil
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (n : ℕ) :
    taoSection7SourceHitPathPoint j s pre [] n =
      taoSection7SourceHitPoint j s pre := by
  cases n <;> rfl

@[simp] theorem taoSection7SourceHitPathPoint_cons_succ
    (j : ℕ+) (s : ℕ) (pre next : List ℕ) (rest : List (List ℕ))
    (n : ℕ) :
    taoSection7SourceHitPathPoint j s pre (next :: rest) (n + 1) =
      taoSection7SourceHitPathPoint
        (taoSection7ShiftIndex j (pre.length + 1))
        (s + pre.sum + 3) next rest n := by
  rfl

theorem taoSection7RenewalPathPoint_sourceHit_eq
    (j : ℕ+) (s : ℕ) :
    ∀ (pre : List ℕ) (pres : List (List ℕ)) (n : ℕ),
      taoSection7RenewalPathPoint
          (taoSection7SourceHitPoint j s pre)
          (taoSection7HoldIncrementsOfPrefixes pres) n =
        taoSection7SourceHitPathPoint j s pre pres n := by
  intro pre pres
  induction pres generalizing j s pre with
  | nil =>
      intro n
      cases n <;> simp [taoSection7HoldIncrementsOfPrefixes]
  | cons next rest ih =>
      intro n
      cases n with
      | zero =>
          simp [taoSection7HoldIncrementsOfPrefixes]
      | succ n =>
          simp [taoSection7HoldIncrementsOfPrefixes,
            taoSection7SourceHitPathPoint]
          rw [← taoSection7SourceHitPoint_tail_eq_add]
          exact ih (taoSection7ShiftIndex j (pre.length + 1))
            (s + pre.sum + 3) next n

theorem taoSection7RenewalPathPoint_sourceHit_toPoint_eq
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ)) (n : ℕ) :
    (taoSection7RenewalPathPoint
        (taoSection7SourceHitPoint j s pre)
        (taoSection7HoldIncrementsOfPrefixes pres) n).toPoint =
      (taoSection7SourceHitPathPoint j s pre pres n).toPoint := by
  rw [taoSection7RenewalPathPoint_sourceHit_eq]

theorem taoSection7RenewalPathPoint_sourceHit_toPoint_l_eq
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ)) (n : ℕ) :
    (taoSection7RenewalPathPoint
        (taoSection7SourceHitPoint j s pre)
        (taoSection7HoldIncrementsOfPrefixes pres) n).toPoint.l =
      (taoSection7SourceHitPathPoint j s pre pres n).toPoint.l := by
  rw [taoSection7RenewalPathPoint_sourceHit_toPoint_eq]

/--
Source-hit-path version of the concrete-height-exit vertical-growth bridge.
The finite suffix-length hypothesis is explicit: `candidate - q <= pres.length`.
-/
theorem taoSection7Case3_sourceHitPathVerticalGrowth_of_concreteHeightExit_sourcePrefixes
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {A q candidate : ℕ}
    (hcandidate :
      taoSection7Case3HeightExitBound
        (taoSection7Case3ExitGapBound A) q < candidate)
    (hlen : candidate - q ≤ pres.length) :
    taoSection7Case3LargeTriangleBound A q ≤
      ((((taoSection7SourceHitPathPoint j s pre pres
          (candidate - q)).toPoint.l -
        (taoSection7SourceHitPoint j s pre).toPoint.l : ℤ) : ℝ) *
          Real.log 2) := by
  have hrenew :
      taoSection7Case3LargeTriangleBound A q ≤
        ((((taoSection7RenewalPathPoint
            (taoSection7SourceHitPoint j s pre)
            (taoSection7HoldIncrementsOfPrefixes pres)
            (candidate - q)).toPoint.l -
          (taoSection7SourceHitPoint j s pre).toPoint.l : ℤ) : ℝ) *
            Real.log 2) :=
    taoSection7Case3_sourceVerticalGrowth_of_concreteHeightExit_sourcePrefixes
      (p := taoSection7SourceHitPoint j s pre) hcandidate hlen
  have hpath :
      taoSection7RenewalPathPoint
          (taoSection7SourceHitPoint j s pre)
          (taoSection7HoldIncrementsOfPrefixes pres) (candidate - q) =
        taoSection7SourceHitPathPoint j s pre pres (candidate - q) :=
    taoSection7RenewalPathPoint_sourceHit_eq j s pre pres
      (candidate - q)
  simpa [hpath] using hrenew

theorem taoSection7Case3_sourceHitPathVerticalGrowth_of_scale_sourcePrefixes
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {q candidate : ℕ}
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hcandidate :
      taoSection7Case3HeightExitBound gapBound q < candidate)
    (hlen : candidate - q ≤ pres.length) :
    bound q ≤
      ((((taoSection7SourceHitPathPoint j s pre pres
          (candidate - q)).toPoint.l -
        (taoSection7SourceHitPoint j s pre).toPoint.l : ℤ) : ℝ) *
          Real.log 2) := by
  have hrenew :
      bound q ≤
        ((((taoSection7RenewalPathPoint
            (taoSection7SourceHitPoint j s pre)
            (taoSection7HoldIncrementsOfPrefixes pres)
            (candidate - q)).toPoint.l -
          (taoSection7SourceHitPoint j s pre).toPoint.l : ℤ) : ℝ) *
            Real.log 2) :=
    taoSection7Case3_sourceVerticalGrowth_of_scale_sourcePrefixes
      (p := taoSection7SourceHitPoint j s pre) hscale hcandidate hlen
  have hpath :
      taoSection7RenewalPathPoint
          (taoSection7SourceHitPoint j s pre)
          (taoSection7HoldIncrementsOfPrefixes pres) (candidate - q) =
        taoSection7SourceHitPathPoint j s pre pres (candidate - q) :=
    taoSection7RenewalPathPoint_sourceHit_eq j s pre pres
      (candidate - q)
  simpa [hpath] using hrenew

/--
The source suffix after pivot `q` covers all offsets below `P`.  Since offset
`q` is path index `0`, a suffix with `pres.length` following blocks covers
offsets through `q + pres.length`.
-/
def taoSection7SourceSuffixCoversWindow
    (q P : ℕ) (pres : List (List ℕ)) : Prop :=
  P ≤ q + pres.length + 1

theorem taoSection7_candidate_sub_le_sourceSuffixLength_of_lt_sourceWindow
    {q candidate : ℕ} {pres : List (List ℕ)}
    (hcandidate : candidate < q + pres.length + 1) :
    candidate - q ≤ pres.length := by
  omega

theorem taoSection7_candidate_sub_le_sourceSuffixLength_of_lt_window
    {q candidate P : ℕ} {pres : List (List ℕ)}
    (hcandidate_lt_P : candidate < P)
    (hcoverage : taoSection7SourceSuffixCoversWindow q P pres) :
    candidate - q ≤ pres.length := by
  exact
    taoSection7_candidate_sub_le_sourceSuffixLength_of_lt_sourceWindow
      (q := q) (candidate := candidate) (pres := pres)
      (lt_of_lt_of_le hcandidate_lt_P hcoverage)

/--
Later-search membership plus q-room gives `candidate < P`; source-suffix window
coverage then supplies the finite path length bound needed by source-hit path
consumers.
-/
theorem taoSection7Case3_laterSearch_mem_sourceSuffixLength
    {gapBound : ℕ → ℕ} {P threshold q candidate : ℕ}
    {pres : List (List ℕ)}
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hcandidate_mem :
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold))
    (hcoverage : taoSection7SourceSuffixCoversWindow q P pres) :
    candidate - q ≤ pres.length := by
  have hcandidate_lt_P :
      candidate < P :=
    (taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
      hroom hcandidate_mem).2
  exact
    taoSection7_candidate_sub_le_sourceSuffixLength_of_lt_window
      hcandidate_lt_P hcoverage

/--
Low-window plus search-room produces a later non-white candidate whose source
suffix index is within range, assuming the suffix covers the whole `P` window.
This remains support-only: it does not prove q-room, source path coverage, or
the source suffix coverage hypothesis.
-/
theorem taoSection7Case3_exists_later_nonwhite_after_exit_with_sourceSuffixLength
    (W : ℕ → Prop) [DecidablePred W]
    {gapBound : ℕ → ℕ} {P threshold q : ℕ}
    {pres : List (List ℕ)}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hcoverage : taoSection7SourceSuffixCoversWindow q P pres) :
    ∃ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) ∧
        ¬ W candidate ∧
          taoSection7Case3HeightExitBound gapBound q < candidate ∧
            candidate < P ∧ candidate - q ≤ pres.length := by
  rcases taoSection7Case3_exists_later_nonwhite_after_exit_of_searchRoom
      W hlow hroom with
    ⟨candidate, hcandidate_mem, hnotW, hstrict, hltP⟩
  exact
    ⟨candidate, hcandidate_mem, hnotW, hstrict, hltP,
      taoSection7_candidate_sub_le_sourceSuffixLength_of_lt_window
        hltP hcoverage⟩

/--
Local-endpoint exit-height/source-path adapter.  This avoids a global shifted
`pointAt` model and only rewrites the two endpoints needed by the existing
triangle-exit consumer.  The finite suffix-length gate remains explicit as
`candidate - q <= pres.length`.
-/
theorem taoSection7Case3_sourceHitPath_exitHeight_of_concreteHeightExit
    {pointAt : ℕ → TaoSection7Point}
    {old : TaoSection7Triangle}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {A q candidate : ℕ}
    (hpoint_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint)
    (hpoint_candidate :
      pointAt candidate =
        (taoSection7SourceHitPathPoint j s pre pres
          (candidate - q)).toPoint)
    (hmem_old : old.Mem (pointAt q))
    (hsize : old.size < taoSection7Case3LargeTriangleBound A q)
    (hcandidate :
      taoSection7Case3HeightExitBound
        (taoSection7Case3ExitGapBound A) q < candidate)
    (hlen : candidate - q ≤ pres.length) :
    old.cornerL < (pointAt candidate).l := by
  have hgrowth_source :
      taoSection7Case3LargeTriangleBound A q ≤
        ((((taoSection7SourceHitPathPoint j s pre pres
            (candidate - q)).toPoint.l -
          (taoSection7SourceHitPoint j s pre).toPoint.l : ℤ) : ℝ) *
            Real.log 2) :=
    taoSection7Case3_sourceHitPathVerticalGrowth_of_concreteHeightExit_sourcePrefixes
      hcandidate hlen
  have hgrowth_pointAt :
      taoSection7Case3LargeTriangleBound A q ≤
        ((((pointAt candidate).l - (pointAt q).l : ℤ) : ℝ) *
            Real.log 2) := by
    simpa [hpoint_q, hpoint_candidate] using hgrowth_source
  exact
    taoSection7Case3_cornerL_lt_of_mem_source_bound_and_vertical_growth
      hmem_old hsize hgrowth_pointAt

theorem taoSection7Case3_sourceHitPath_exitHeight_of_scale
    {pointAt : ℕ → TaoSection7Point}
    {old : TaoSection7Triangle}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {q candidate : ℕ}
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hpoint_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint)
    (hpoint_candidate :
      pointAt candidate =
        (taoSection7SourceHitPathPoint j s pre pres
          (candidate - q)).toPoint)
    (hmem_old : old.Mem (pointAt q))
    (hsize : old.size < bound q)
    (hcandidate :
      taoSection7Case3HeightExitBound gapBound q < candidate)
    (hlen : candidate - q ≤ pres.length) :
    old.cornerL < (pointAt candidate).l := by
  have hgrowth_source :
      bound q ≤
        ((((taoSection7SourceHitPathPoint j s pre pres
            (candidate - q)).toPoint.l -
          (taoSection7SourceHitPoint j s pre).toPoint.l : ℤ) : ℝ) *
            Real.log 2) :=
    taoSection7Case3_sourceHitPathVerticalGrowth_of_scale_sourcePrefixes
      hscale hcandidate hlen
  have hgrowth_pointAt :
      bound q ≤
        ((((pointAt candidate).l - (pointAt q).l : ℤ) : ℝ) *
            Real.log 2) := by
    simpa [hpoint_q, hpoint_candidate] using hgrowth_source
  exact
    taoSection7Case3_cornerL_lt_of_mem_and_vertical_growth_log2_gt_size
      hmem_old (lt_of_lt_of_le hsize hgrowth_pointAt)

/--
Abstract-`pointAt` version of the source-hit black-pivot consumer.  It only
specializes the existing black-pivot theorem after the caller identifies the
pivot and candidate endpoints with the concrete source-hit path and supplies
the finite suffix-length bound.
-/
theorem taoSection7Case3_exists_blackPivotStep_of_pointAt_sourceHitPath_concreteHeightExit
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {old : TaoSection7Triangle}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {A q candidate : ℕ}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hblack : black (pointAt candidate))
    (hmem_old : old.Mem (pointAt q))
    (hsize : old.size < taoSection7Case3LargeTriangleBound A q)
    (hpoint_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint)
    (hpoint_candidate :
      pointAt candidate =
        (taoSection7SourceHitPathPoint j s pre pres
          (candidate - q)).toPoint)
    (hcandidate :
      taoSection7Case3HeightExitBound
        (taoSection7Case3ExitGapBound A) q < candidate)
    (hlen : candidate - q ≤ pres.length) :
    ∃ Γ : TaoSection7Triangle,
      taoSection7Case3BlackPivotStep black family pointAt old Γ candidate := by
  have hgrowth_source :
      taoSection7Case3LargeTriangleBound A q ≤
        ((((taoSection7SourceHitPathPoint j s pre pres
            (candidate - q)).toPoint.l -
          (taoSection7SourceHitPoint j s pre).toPoint.l : ℤ) : ℝ) *
            Real.log 2) :=
    taoSection7Case3_sourceHitPathVerticalGrowth_of_concreteHeightExit_sourcePrefixes
      hcandidate hlen
  have hgrowth_pointAt :
      taoSection7Case3LargeTriangleBound A q ≤
        ((((pointAt candidate).l - (pointAt q).l : ℤ) : ℝ) *
            Real.log 2) := by
    simpa [hpoint_q, hpoint_candidate] using hgrowth_source
  exact
    taoSection7Case3_exists_blackPivotStep_of_source_bound_and_growth
      hcover hblack hmem_old hsize hgrowth_pointAt

theorem taoSection7Case3_exists_blackPivotStep_of_pointAt_sourceHitPath_scale
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {old : TaoSection7Triangle}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {q candidate : ℕ}
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hblack : black (pointAt candidate))
    (hmem_old : old.Mem (pointAt q))
    (hsize : old.size < bound q)
    (hpoint_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint)
    (hpoint_candidate :
      pointAt candidate =
        (taoSection7SourceHitPathPoint j s pre pres
          (candidate - q)).toPoint)
    (hcandidate :
      taoSection7Case3HeightExitBound gapBound q < candidate)
    (hlen : candidate - q ≤ pres.length) :
    ∃ Γ : TaoSection7Triangle,
      taoSection7Case3BlackPivotStep black family pointAt old Γ candidate := by
  exact
    taoSection7Case3_exists_blackPivotStep_of_exit_height
      hcover hblack
      (taoSection7Case3_sourceHitPath_exitHeight_of_scale
        (hscale := hscale) (hpoint_q := hpoint_q)
        (hpoint_candidate := hpoint_candidate) (hmem_old := hmem_old)
        (hsize := hsize) (hcandidate := hcandidate) (hlen := hlen))

/--
Later-search, source-suffix coverage, local source-hit endpoint identification,
and source white/black transport produce the black-pivot package for a concrete
later candidate.  Q-room/search-room, source-suffix coverage, and endpoint
identification remain explicit hypotheses.
-/
theorem taoSection7Case3_exists_laterBlackPivotStep_of_searchRoom_sourceHitPath
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hcoverage : taoSection7SourceSuffixCoversWindow q P pres)
    (hpoint_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint)
    (hpoint_candidate :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q + threshold) →
        pointAt candidate =
          (taoSection7SourceHitPathPoint j s pre pres
            (candidate - q)).toPoint)
    (hmem_old : old.Mem (pointAt q))
    (hsize : old.size < taoSection7Case3LargeTriangleBound A q)
    (hWwhite :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q + threshold) →
          (W candidate ↔
            taoSection7SourceWhitePoint n xi epsilon (pointAt candidate)))
    (hdomain :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q + threshold) →
          taoSection7SourcePointInDomain J (pointAt candidate))
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
  rcases taoSection7Case3_exists_later_nonwhite_after_exit_of_searchRoom
      W hlow hroom with
    ⟨candidate, hcandidate_mem, hnotW, hstrict, hcandidate_lt_P⟩
  have hlen : candidate - q ≤ pres.length :=
    taoSection7_candidate_sub_le_sourceSuffixLength_of_lt_window
      hcandidate_lt_P hcoverage
  have hnotWhite :
      ¬ taoSection7SourceWhitePoint n xi epsilon (pointAt candidate) := by
    intro hwhite
    exact hnotW ((hWwhite candidate hcandidate_mem).2 hwhite)
  have hblack :
      taoSection7SourceBlackInDomain n xi epsilon J (pointAt candidate) :=
    taoSection7SourceBlackInDomain_of_not_sourceWhitePoint
      (hdomain candidate hcandidate_mem) hnotWhite
  rcases
      taoSection7Case3_exists_blackPivotStep_of_pointAt_sourceHitPath_concreteHeightExit
        (hcover := hcover) (hblack := hblack) (hmem_old := hmem_old)
        (hsize := hsize) (hpoint_q := hpoint_q)
        (hpoint_candidate := hpoint_candidate candidate hcandidate_mem)
        (hcandidate := hstrict) (hlen := hlen) with
    ⟨Γ, hΓ⟩
  exact
    ⟨candidate, hcandidate_mem, hnotW, hstrict, hcandidate_lt_P, hlen, Γ, hΓ⟩

theorem taoSection7Case3_exists_laterBlackPivotStep_of_searchRoom_sourceHitPath_scale
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hcoverage : taoSection7SourceSuffixCoversWindow q P pres)
    (hpoint_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint)
    (hpoint_candidate :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart gapBound q)
          (taoSection7Case3LaterSearchStart gapBound q + threshold) →
        pointAt candidate =
          (taoSection7SourceHitPathPoint j s pre pres
            (candidate - q)).toPoint)
    (hmem_old : old.Mem (pointAt q))
    (hsize : old.size < bound q)
    (hWwhite :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart gapBound q)
          (taoSection7Case3LaterSearchStart gapBound q + threshold) →
          (W candidate ↔
            taoSection7SourceWhitePoint n xi epsilon (pointAt candidate)))
    (hdomain :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart gapBound q)
          (taoSection7Case3LaterSearchStart gapBound q + threshold) →
          taoSection7SourcePointInDomain J (pointAt candidate))
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
  rcases taoSection7Case3_exists_later_nonwhite_after_exit_of_searchRoom
      W hlow hroom with
    ⟨candidate, hcandidate_mem, hnotW, hstrict, hcandidate_lt_P⟩
  have hlen : candidate - q ≤ pres.length :=
    taoSection7_candidate_sub_le_sourceSuffixLength_of_lt_window
      hcandidate_lt_P hcoverage
  have hnotWhite :
      ¬ taoSection7SourceWhitePoint n xi epsilon (pointAt candidate) := by
    intro hwhite
    exact hnotW ((hWwhite candidate hcandidate_mem).2 hwhite)
  have hblack :
      taoSection7SourceBlackInDomain n xi epsilon J (pointAt candidate) :=
    taoSection7SourceBlackInDomain_of_not_sourceWhitePoint
      (hdomain candidate hcandidate_mem) hnotWhite
  rcases
      taoSection7Case3_exists_blackPivotStep_of_pointAt_sourceHitPath_scale
        (hscale := hscale) (hcover := hcover) (hblack := hblack)
        (hmem_old := hmem_old) (hsize := hsize) (hpoint_q := hpoint_q)
        (hpoint_candidate := hpoint_candidate candidate hcandidate_mem)
        (hcandidate := hstrict) (hlen := hlen) with
    ⟨Γ, hΓ⟩
  exact
    ⟨candidate, hcandidate_mem, hnotW, hstrict, hcandidate_lt_P, hlen, Γ, hΓ⟩

end Tao
end Erdos1135
