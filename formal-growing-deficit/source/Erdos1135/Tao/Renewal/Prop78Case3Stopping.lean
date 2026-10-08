import Erdos1135.Tao.Renewal.Prop78Case3ActiveTriangle
import Erdos1135.Tao.Renewal.Prop78Case3CutoffAlignment

/-!
# Section 7 Case 3 Q-Relative First-Stopping Support

This module records the q-relative first-hit/first-stopping support for
Proposition 7.8 Case 3.  It minimizes only after
the current pivot index `q`.  That shape is closer to Tao's recursive stopping
times `t_i`, which are first hits after the previous triangle top has been
exceeded, rather than first hits from absolute time zero.

It is support-only.  It preserves the later-window facts around the produced
black-pivot candidate and makes source rebase provenance at the minimized
first hit explicit.  It does not produce source-path data, source `(7.11)`,
the source `r`/`t_R` bridge, Lemma 7.9, Lemma 7.10, Tao's many-whites
inequality, `(7.41)`, Proposition 7.8, Proposition 7.3/7.1, or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

/-- A post-exit triangle hit after the old triangle. -/
def TaoSection7Case3AfterTriangleHit
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (old : TaoSection7Triangle) (t : ℕ) : Prop :=
  old.cornerL < (pointAt t).l ∧
    ∃ Γ : TaoSection7Triangle, Γ ∈ family ∧ Γ.Mem (pointAt t)

/--
The first post-exit triangle hit after the pivot index `q`.

This is deliberately relative to `q`; it avoids treating unrelated earlier hits
in an absolute `pointAt` path as the next stop of Tao's local iteration.
-/
def TaoSection7Case3FirstAfterTriangleHitFrom
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (old : TaoSection7Triangle) (q t : ℕ) : Prop :=
  q < t ∧
    TaoSection7Case3AfterTriangleHit pointAt family old t ∧
      ∀ s : ℕ, q < s → s < t →
        ¬ TaoSection7Case3AfterTriangleHit pointAt family old s

theorem taoSection7_exists_first_nat_between_of_candidate
    (Pred : ℕ → Prop) [DecidablePred Pred] {start candidate : ℕ}
    (hstart : start < candidate)
    (hcandidate : Pred candidate) :
    ∃ first : ℕ, start < first ∧ first ≤ candidate ∧ Pred first ∧
      ∀ k : ℕ, start < k → k < first → ¬ Pred k := by
  let S : Finset ℕ := Finset.filter Pred (Finset.Icc (start + 1) candidate)
  have hnonempty : S.Nonempty := by
    refine ⟨candidate, ?_⟩
    simp [S, hcandidate, Nat.succ_le_iff.mpr hstart]
  let first : ℕ := S.min' hnonempty
  have hfirst_mem : first ∈ S := Finset.min'_mem S hnonempty
  have hfirst_mem_Icc :
      first ∈ Finset.Icc (start + 1) candidate :=
    (Finset.mem_filter.1 hfirst_mem).1
  have hfirst_bounds := Finset.mem_Icc.mp hfirst_mem_Icc
  have hstart_lt_first : start < first := Nat.lt_of_succ_le hfirst_bounds.1
  have hfirst_le_candidate : first ≤ candidate := hfirst_bounds.2
  have hfirst_pred : Pred first := (Finset.mem_filter.1 hfirst_mem).2
  refine
    ⟨first, hstart_lt_first, hfirst_le_candidate, hfirst_pred, ?_⟩
  intro k hk_start hk_first hpred
  have hk_mem : k ∈ S := by
    have hk_lower : start + 1 ≤ k := Nat.succ_le_iff.mpr hk_start
    have hk_upper : k ≤ candidate :=
      (Nat.le_of_lt hk_first).trans hfirst_le_candidate
    simp [S, hk_lower, hk_upper, hpred]
  have hmin_le : first ≤ k := Finset.min'_le S k hk_mem
  omega

theorem taoSection7Case3_afterTriangleHit_of_blackPivotStep
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hstep :
      taoSection7Case3BlackPivotStep black family pointAt old Γ candidate) :
    TaoSection7Case3AfterTriangleHit pointAt family old candidate := by
  exact ⟨hstep.1, Γ, hstep.2.2.1, hstep.2.2.2.1⟩

theorem taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_candidate
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {q candidate : ℕ}
    (hq_candidate : q < candidate)
    (hcandidate :
      TaoSection7Case3AfterTriangleHit pointAt family old candidate) :
    ∃ first : ℕ, first ≤ candidate ∧
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first := by
  classical
  rcases taoSection7_exists_first_nat_between_of_candidate
      (TaoSection7Case3AfterTriangleHit pointAt family old)
      hq_candidate hcandidate with
    ⟨first, hq_first, hfirst_le, hfirst, hminimal⟩
  exact ⟨first, hfirst_le, hq_first, hfirst, hminimal⟩

theorem taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_blackPivotStep
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {old Γ : TaoSection7Triangle} {q candidate : ℕ}
    (hq_candidate : q < candidate)
    (hstep :
      taoSection7Case3BlackPivotStep black family pointAt old Γ candidate) :
    ∃ first : ℕ, first ≤ candidate ∧
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first :=
  taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_candidate
    hq_candidate
    (taoSection7Case3_afterTriangleHit_of_blackPivotStep hstep)

theorem taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_activeBlackPivotStep
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A q : ℕ} {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hq_candidate : q < candidate)
    (hstep :
      TaoSection7Case3ActiveBlackPivotStep
        black family pointAt A q old Γ candidate) :
    ∃ first : ℕ, first ≤ candidate ∧
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first :=
  taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_blackPivotStep
    hq_candidate hstep.pivot_step

theorem taoSection7Case3_afterTriangleHit_new_triangle
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {t : ℕ}
    (hhit : TaoSection7Case3AfterTriangleHit pointAt family old t) :
    ∃ Γ : TaoSection7Triangle,
      Γ ∈ family ∧ Γ.Mem (pointAt t) ∧ Γ ≠ old := by
  rcases hhit with ⟨hexit_height, Γ, hΓ, hmemΓ⟩
  refine ⟨Γ, hΓ, hmemΓ, ?_⟩
  intro hΓ_eq
  subst hΓ_eq
  exact taoSection7Case3_not_mem_of_cornerL_lt hexit_height hmemΓ

theorem taoSection7Case3_firstAfterTriangleHitFrom_new_triangle
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {q first : ℕ}
    (hfirst :
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first) :
    ∃ Γ : TaoSection7Triangle,
      Γ ∈ family ∧ Γ.Mem (pointAt first) ∧ Γ ≠ old :=
  taoSection7Case3_afterTriangleHit_new_triangle hfirst.2.1

theorem taoSection7Case3_firstAfterTriangleHitFrom_black_of_cover
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {q first : ℕ}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hfirst :
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first) :
    black (pointAt first) := by
  exact (hcover (pointAt first)).mpr hfirst.2.1.2

theorem taoSection7Case3_exists_firstAfterTriangleHitFromWithNewTriangle_le_of_activeBlackPivotStep
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A q : ℕ} {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hq_candidate : q < candidate)
    (hstep :
      TaoSection7Case3ActiveBlackPivotStep
        black family pointAt A q old Γ candidate) :
    ∃ first : ℕ, first ≤ candidate ∧
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first ∧
        ∃ Γ' : TaoSection7Triangle,
          Γ' ∈ family ∧ Γ'.Mem (pointAt first) ∧ Γ' ≠ old := by
  rcases
      taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_activeBlackPivotStep
        hq_candidate hstep with
    ⟨first, hfirst_le, hfirst⟩
  exact
    ⟨first, hfirst_le, hfirst,
      taoSection7Case3_firstAfterTriangleHitFrom_new_triangle hfirst⟩

/--
Source-data-level wrapper: the current source-path data and active-triangle
state produce a bounded later candidate, and from that candidate a first
post-pivot triangle hit no later than the candidate.
-/
theorem taoSection7Case3_exists_firstAfterTriangleHitFromWithNewTriangle_of_sourcePathData
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
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
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
              ∃ first : ℕ, first ≤ candidate ∧
                TaoSection7Case3FirstAfterTriangleHitFrom
                  pointAt family old q first ∧
                  ∃ Γ' : TaoSection7Triangle,
                    Γ' ∈ family ∧ Γ'.Mem (pointAt first) ∧ Γ' ≠ old := by
  rcases
      taoSection7Case3_exists_activeBlackPivotStep_of_sourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hlow hroom hactive hcover with
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ, hstep⟩
  have hq_candidate : q < candidate := by
    dsimp [taoSection7Case3HeightExitBound] at hstrict
    omega
  rcases
      taoSection7Case3_exists_firstAfterTriangleHitFromWithNewTriangle_le_of_activeBlackPivotStep
        hq_candidate hstep with
    ⟨first, hfirst_le, hfirst, hnew⟩
  exact
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen,
      first, hfirst_le, hfirst, hnew⟩

/--
Source-data-level wrapper with the blackness of the minimized first hit exposed.
This uses the bidirectional `TaoSection7TriangleFamilyCoverBlack` hypothesis; it
does not assume blackness separately at `first`.
-/
theorem taoSection7Case3_exists_firstAfterTriangleHitFromWithBlack_of_sourcePathData
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
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
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
              ∃ first : ℕ, first ≤ candidate ∧ first < P ∧
                taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) ∧
                TaoSection7Case3FirstAfterTriangleHitFrom
                  pointAt family old q first ∧
                  ∃ Γ' : TaoSection7Triangle,
                    Γ' ∈ family ∧ Γ'.Mem (pointAt first) ∧ Γ' ≠ old := by
  rcases
      taoSection7Case3_exists_firstAfterTriangleHitFromWithNewTriangle_of_sourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hlow hroom hactive hcover with
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, first, hfirst_le,
      hfirst, hnew⟩
  have hfirst_ltP : first < P := lt_of_le_of_lt hfirst_le hltP
  have hblack :
      taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) :=
    taoSection7Case3_firstAfterTriangleHitFrom_black_of_cover hcover hfirst
  exact
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen,
      first, hfirst_le, hfirst_ltP, hblack, hfirst, hnew⟩

/--
Accepted transition at the minimized post-pivot first hit.

This is narrower than `TaoSection7Case3AcceptedTriangleTransition`: the
transition target is the first triangle hit after `q`, not merely the later
black candidate used to prove existence.
-/
structure TaoSection7Case3FirstHitAcceptedTransition
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    (q : ℕ) (old Γ : TaoSection7Triangle) (first : ℕ) : Prop where
  first_hit :
    TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first
  first_black : black (pointAt first)
  new_mem_family : Γ ∈ family
  new_mem : Γ.Mem (pointAt first)
  new_ne_old : Γ ≠ old
  accepted : Accepts q old first Γ

theorem taoSection7Case3_exists_firstHitAcceptedTransition_of_firstHitFrom
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {q first : ℕ} {old : TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hfirst :
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first)
    (haccept :
      ∀ Γ : TaoSection7Triangle,
        Γ ∈ family →
          Γ.Mem (pointAt first) →
            Γ ≠ old →
              black (pointAt first) →
                Accepts q old first Γ) :
    ∃ Γ : TaoSection7Triangle,
      TaoSection7Case3FirstHitAcceptedTransition
        black family pointAt Accepts q old Γ first := by
  have hblack : black (pointAt first) :=
    taoSection7Case3_firstAfterTriangleHitFrom_black_of_cover hcover hfirst
  rcases taoSection7Case3_firstAfterTriangleHitFrom_new_triangle hfirst with
    ⟨Γ, hΓ, hmem, hne⟩
  exact
    ⟨Γ, hfirst, hblack, hΓ, hmem, hne,
      haccept Γ hΓ hmem hne hblack⟩

/--
Package a q-relative first-hit accepted transition as the start-based strict
bounded advance consumed by the Case 3 one-step event adapter.

The start-based recurrence step and budget remain explicit hypotheses; they
are not consequences of first-hit acceptance alone.
-/
theorem taoSection7Case3_strictBoundedAdvance_of_firstHitAcceptedTransition
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {B : ℕ → ℕ} {Step : ℕ → ℕ → Prop}
    {start threshold q first : ℕ}
    {old Γ : TaoSection7Triangle}
    (hq : q ∈ Finset.Icc start (start + threshold))
    (hacc :
      TaoSection7Case3FirstHitAcceptedTransition
        black family pointAt Accepts q old Γ first)
    (hstep : Step start first)
    (hbound : first ≤ B start) :
    ∃ next : ℕ,
      taoSection7Case3StrictBoundedAdvance B Step start next := by
  refine ⟨first, hstep, ?_, hbound⟩
  exact lt_of_le_of_lt (Finset.mem_Icc.mp hq).1 hacc.first_hit.1

/--
Source-data-level accepted-transition wrapper at the minimized first hit.

The caller still supplies the actual stopping/iteration acceptance theorem;
this wrapper only ensures that theorem is applied to the q-relative first
post-pivot triangle hit and carries the candidate bound that produced it.
-/
theorem taoSection7Case3_exists_firstHitAcceptedTransition_of_sourcePathData
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
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
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (haccept :
      ∀ first Γ,
        first < P →
          taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
            TaoSection7Case3FirstAfterTriangleHitFrom
              pointAt family old q first →
              Γ ∈ family →
                Γ.Mem (pointAt first) →
                  Γ ≠ old →
                    Accepts q old first Γ) :
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
              ∃ first Γ,
                first ≤ candidate ∧ first < P ∧
                  TaoSection7Case3FirstHitAcceptedTransition
                    (taoSection7SourceBlackInDomain n xi epsilon J)
                    family pointAt Accepts q old Γ first := by
  rcases
      taoSection7Case3_exists_firstAfterTriangleHitFromWithBlack_of_sourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hlow hroom hactive hcover with
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, first, hfirst_le,
      hfirst_ltP, hblack, hfirst, hnew⟩
  rcases hnew with ⟨Γ, hΓ, hΓmem, hΓne⟩
  refine
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen,
      first, Γ, hfirst_le, hfirst_ltP, ?_⟩
  exact
    ⟨hfirst, hblack, hΓ, hΓmem, hΓne,
      haccept first Γ hfirst_ltP hblack hfirst hΓ hΓmem hΓne⟩

/--
Active black-pivot package that retains the later-search/window facts returned
by the source-data producer.

This avoids treating the bare active step as if it still remembered the
candidate bounds needed by later first-stopping and `t_R <= P` plumbing.
-/
structure TaoSection7Case3ActiveBlackPivotStepInLaterWindow
    (W : ℕ → Prop)
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (A threshold P q sourceLength : ℕ)
    (old Γ : TaoSection7Triangle) (candidate : ℕ) : Prop where
  mem_later_window :
    candidate ∈ Finset.Icc
      (taoSection7Case3LaterSearchStart
        (taoSection7Case3ExitGapBound A) q)
      (taoSection7Case3LaterSearchStart
        (taoSection7Case3ExitGapBound A) q + threshold)
  not_white : ¬ W candidate
  strict_exit :
    taoSection7Case3HeightExitBound
      (taoSection7Case3ExitGapBound A) q < candidate
  candidate_ltP : candidate < P
  source_length_bound : candidate - q ≤ sourceLength
  active_step :
    TaoSection7Case3ActiveBlackPivotStep
      black family pointAt A q old Γ candidate

theorem taoSection7Case3_activeBlackPivotStepInLaterWindow_q_lt_candidate
    {W : ℕ → Prop}
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A threshold P q sourceLength : ℕ}
    {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hstep :
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W black family pointAt A threshold P q sourceLength
        old Γ candidate) :
    q < candidate := by
  have hstrict := hstep.strict_exit
  dsimp [taoSection7Case3HeightExitBound] at hstrict
  omega

/--
Generic-scale version of
`TaoSection7Case3ActiveBlackPivotStepInLaterWindow`.

The later-window and strict-exit facts are measured with the caller-supplied
`gapBound`, while the active triangle threshold is measured with the
caller-supplied real `bound`.
-/
structure TaoSection7Case3ActiveBlackPivotStepInLaterWindowWithBound
    (W : ℕ → Prop)
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (bound : ℕ → ℝ) (gapBound : ℕ → ℕ)
    (threshold P q sourceLength : ℕ)
    (old Γ : TaoSection7Triangle) (candidate : ℕ) : Prop where
  mem_later_window :
    candidate ∈ Finset.Icc
      (taoSection7Case3LaterSearchStart gapBound q)
      (taoSection7Case3LaterSearchStart gapBound q + threshold)
  not_white : ¬ W candidate
  strict_exit : taoSection7Case3HeightExitBound gapBound q < candidate
  candidate_ltP : candidate < P
  source_length_bound : candidate - q ≤ sourceLength
  active_step :
    TaoSection7Case3ActiveBlackPivotStepWithBound
      black family pointAt bound q old Γ candidate

theorem taoSection7Case3_activeBlackPivotStepInLaterWindowWithBound_q_lt_candidate
    {W : ℕ → Prop}
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {threshold P q sourceLength : ℕ}
    {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hstep :
      TaoSection7Case3ActiveBlackPivotStepInLaterWindowWithBound
        W black family pointAt bound gapBound threshold P q sourceLength
        old Γ candidate) :
    q < candidate := by
  have hstrict := hstep.strict_exit
  dsimp [taoSection7Case3HeightExitBound] at hstrict
  omega

theorem taoSection7Case3_exists_activeBlackPivotStepInLaterWindow_of_sourcePathData
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
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt A threshold P q pres.length old Γ candidate := by
  rcases
      taoSection7Case3_exists_activeBlackPivotStep_of_sourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hlow hroom hactive hcover with
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ, hstep⟩
  exact
    ⟨candidate, Γ, hmem, hnotW, hstrict, hltP, hlen, hstep⟩

theorem taoSection7Case3_exists_activeBlackPivotStepInLaterWindow_of_sourcePathData_scale
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
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindowWithBound
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt bound gapBound threshold P q pres.length
        old Γ candidate := by
  rcases
      taoSection7Case3_exists_activeBlackPivotStep_of_sourcePathData_scale
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive hcover with
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ, hstep⟩
  exact
    ⟨candidate, Γ, hmem, hnotW, hstrict, hltP, hlen, hstep⟩

theorem taoSection7Case3_exists_firstHitAcceptedTransition_of_activeBlackPivotStepInLaterWindow
    {W : ℕ → Prop}
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {A threshold P q sourceLength : ℕ}
    {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hstep :
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W black family pointAt A threshold P q sourceLength
        old Γ candidate)
    (haccept :
      ∀ first Γ',
        first ≤ candidate →
          first < P →
            black (pointAt first) →
              TaoSection7Case3FirstAfterTriangleHitFrom
                pointAt family old q first →
                Γ' ∈ family →
                  Γ'.Mem (pointAt first) →
                    Γ' ≠ old →
                      Accepts q old first Γ') :
    ∃ first Γ',
      first ≤ candidate ∧ first < P ∧
        TaoSection7Case3FirstHitAcceptedTransition
          black family pointAt Accepts q old Γ' first := by
  have hq_candidate : q < candidate :=
    taoSection7Case3_activeBlackPivotStepInLaterWindow_q_lt_candidate hstep
  rcases
      taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_activeBlackPivotStep
        hq_candidate hstep.active_step with
    ⟨first, hfirst_le, hfirst⟩
  have hfirst_ltP : first < P := lt_of_le_of_lt hfirst_le hstep.candidate_ltP
  have hblack : black (pointAt first) :=
    taoSection7Case3_firstAfterTriangleHitFrom_black_of_cover hcover hfirst
  rcases taoSection7Case3_firstAfterTriangleHitFrom_new_triangle hfirst with
    ⟨Γ', hΓ', hmem, hne⟩
  exact
    ⟨first, Γ', hfirst_le, hfirst_ltP,
      hfirst, hblack, hΓ', hmem, hne,
      haccept first Γ' hfirst_le hfirst_ltP hblack hfirst hΓ' hmem hne⟩

/--
Source provenance for the minimized q-relative first hit.

This is intentionally stronger than the current source-path data interface:
the point equality and suffix-length bound are recorded at the minimized
`first`, not only at the later candidate used to prove existence.
-/
structure TaoSection7Case3FirstHitSourceProvenance
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ))
    (P q : ℕ) (old Γ : TaoSection7Triangle)
    (candidate first : ℕ) : Prop where
  first_le_candidate : first ≤ candidate
  first_ltP : first < P
  first_source :
    pointAt first =
      (taoSection7SourceHitPathPoint j s pre pres (first - q)).toPoint
  first_source_length : first - q ≤ pres.length
  first_hit :
    TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first
  first_black : black (pointAt first)
  new_mem_family : Γ ∈ family
  new_mem : Γ.Mem (pointAt first)
  new_ne_old : Γ ≠ old

theorem taoSection7Case3_exists_firstHitSourceProvenance_of_activeBlackPivotStepInLaterWindow
    {W : ℕ → Prop}
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A threshold P q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hstep :
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W black family pointAt A threshold P q pres.length
        old Γ candidate)
    (hfirst_source :
      ∀ first : ℕ,
        q < first →
          first ≤ candidate →
            pointAt first =
              (taoSection7SourceHitPathPoint j s pre pres
                (first - q)).toPoint) :
    ∃ first Γ',
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ' candidate first := by
  have hq_candidate : q < candidate :=
    taoSection7Case3_activeBlackPivotStepInLaterWindow_q_lt_candidate hstep
  rcases
      taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_activeBlackPivotStep
        hq_candidate hstep.active_step with
    ⟨first, hfirst_le, hfirst⟩
  have hfirst_ltP : first < P := lt_of_le_of_lt hfirst_le hstep.candidate_ltP
  have hblack : black (pointAt first) :=
    taoSection7Case3_firstAfterTriangleHitFrom_black_of_cover hcover hfirst
  have hsource :
      pointAt first =
        (taoSection7SourceHitPathPoint j s pre pres (first - q)).toPoint :=
    hfirst_source first hfirst.1 hfirst_le
  have hlen : first - q ≤ pres.length := by
    exact (Nat.sub_le_sub_right hfirst_le q).trans hstep.source_length_bound
  rcases taoSection7Case3_firstAfterTriangleHitFrom_new_triangle hfirst with
    ⟨Γ', hΓ', hmem, hne⟩
  exact
    ⟨first, Γ', hfirst_le, hfirst_ltP, hsource, hlen,
      hfirst, hblack, hΓ', hmem, hne⟩

theorem taoSection7Case3_firstHit_source_length_of_ltP
    {P q first : ℕ} {pres : List (List ℕ)}
    (hfirst_ltP : first < P)
    (hcoverage : taoSection7SourceSuffixCoversWindow q P pres) :
    first - q ≤ pres.length :=
  taoSection7_candidate_sub_le_sourceSuffixLength_of_lt_window
    hfirst_ltP hcoverage

/--
Variant of first-hit source provenance where the suffix-length bound at `first`
comes from the whole-window suffix coverage, not from the later candidate.

The only genuinely new source-facing premise is the point equality at the
minimized first hit for post-`q` points below `P`.
-/
theorem taoSection7Case3_exists_firstHitSourceProvenance_of_activeBlackPivotStepInLaterWindow_coverage
    {W : ℕ → Prop}
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A threshold P q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hstep :
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W black family pointAt A threshold P q pres.length
        old Γ candidate)
    (hcoverage : taoSection7SourceSuffixCoversWindow q P pres)
    (hfirst_source :
      ∀ first : ℕ,
        q < first →
          first < P →
            pointAt first =
              (taoSection7SourceHitPathPoint j s pre pres
                (first - q)).toPoint) :
    ∃ first Γ',
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ' candidate first := by
  have hq_candidate : q < candidate :=
    taoSection7Case3_activeBlackPivotStepInLaterWindow_q_lt_candidate hstep
  rcases
      taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_activeBlackPivotStep
        hq_candidate hstep.active_step with
    ⟨first, hfirst_le, hfirst⟩
  have hfirst_ltP : first < P := lt_of_le_of_lt hfirst_le hstep.candidate_ltP
  have hblack : black (pointAt first) :=
    taoSection7Case3_firstAfterTriangleHitFrom_black_of_cover hcover hfirst
  have hsource :
      pointAt first =
        (taoSection7SourceHitPathPoint j s pre pres (first - q)).toPoint :=
    hfirst_source first hfirst.1 hfirst_ltP
  have hlen : first - q ≤ pres.length :=
    taoSection7Case3_firstHit_source_length_of_ltP hfirst_ltP hcoverage
  rcases taoSection7Case3_firstAfterTriangleHitFrom_new_triangle hfirst with
    ⟨Γ', hΓ', hmem, hne⟩
  exact
    ⟨first, Γ', hfirst_le, hfirst_ltP, hsource, hlen,
      hfirst, hblack, hΓ', hmem, hne⟩

/--
Generic-scale first-hit provenance from a later-window active black pivot.

This is the first-stopping analogue of the generic active-transition package:
it keeps the minimized first hit tied to the source path while preserving the
caller-supplied `bound/gapBound` window data.
-/
theorem taoSection7Case3_exists_firstHitSourceProvenance_of_activeBlackPivotStepInLaterWindowWithBound_coverage
    {W : ℕ → Prop}
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {threshold P q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hstep :
      TaoSection7Case3ActiveBlackPivotStepInLaterWindowWithBound
        W black family pointAt bound gapBound threshold P q pres.length
        old Γ candidate)
    (hcoverage : taoSection7SourceSuffixCoversWindow q P pres)
    (hfirst_source :
      ∀ first : ℕ,
        q < first →
          first < P →
            pointAt first =
              (taoSection7SourceHitPathPoint j s pre pres
                (first - q)).toPoint) :
    ∃ first Γ',
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ' candidate first := by
  have hq_candidate : q < candidate :=
    taoSection7Case3_activeBlackPivotStepInLaterWindowWithBound_q_lt_candidate
      hstep
  rcases
      taoSection7Case3_exists_firstAfterTriangleHitFrom_le_of_blackPivotStep
        hq_candidate hstep.active_step.pivot_step with
    ⟨first, hfirst_le, hfirst⟩
  have hfirst_ltP : first < P := lt_of_le_of_lt hfirst_le hstep.candidate_ltP
  have hblack : black (pointAt first) :=
    taoSection7Case3_firstAfterTriangleHitFrom_black_of_cover hcover hfirst
  have hsource :
      pointAt first =
        (taoSection7SourceHitPathPoint j s pre pres (first - q)).toPoint :=
    hfirst_source first hfirst.1 hfirst_ltP
  have hlen : first - q ≤ pres.length :=
    taoSection7Case3_firstHit_source_length_of_ltP hfirst_ltP hcoverage
  rcases taoSection7Case3_firstAfterTriangleHitFrom_new_triangle hfirst with
    ⟨Γ', hΓ', hmem, hne⟩
  exact
    ⟨first, Γ', hfirst_le, hfirst_ltP, hsource, hlen,
      hfirst, hblack, hΓ', hmem, hne⟩

/--
Source-data wrapper for first-hit provenance with an explicit wider source
equality premise for the minimized hit.

The current `TaoSection7Case3SourcePathData` fields cover the later-search
candidate.  This wrapper shows the extra hypothesis needed to rebase at the
minimized first hit without assuming it lies in the later-search block.
-/
theorem taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData
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
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfirst_source :
      ∀ candidate first : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q + threshold) →
        ¬ W candidate →
        taoSection7Case3HeightExitBound
          (taoSection7Case3ExitGapBound A) q < candidate →
        candidate < P →
        candidate - q ≤ pres.length →
        q < first →
        first ≤ candidate →
          pointAt first =
            (taoSection7SourceHitPathPoint j s pre pres
              (first - q)).toPoint) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt A threshold P q pres.length old Γ candidate ∧
        ∃ first Γ',
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt j s pre pres P q old Γ' candidate first := by
  rcases
      taoSection7Case3_exists_activeBlackPivotStepInLaterWindow_of_sourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hlow hroom hactive hcover with
    ⟨candidate, Γ, hstep⟩
  have hfirst_source_local :
      ∀ first : ℕ,
        q < first →
          first ≤ candidate →
            pointAt first =
              (taoSection7SourceHitPathPoint j s pre pres
                (first - q)).toPoint := by
    intro first hq_first hfirst_le
    exact
      hfirst_source candidate first hstep.mem_later_window hstep.not_white
        hstep.strict_exit hstep.candidate_ltP hstep.source_length_bound
        hq_first hfirst_le
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_activeBlackPivotStepInLaterWindow
        hcover hstep hfirst_source_local with
    ⟨first, Γ', hfirstProv⟩
  exact ⟨candidate, Γ, hstep, first, Γ', hfirstProv⟩

/--
Source-data wrapper with the sharper source-facing obligation: to rebase at the
minimized first hit, it is enough to identify `pointAt first` with the source
path for every post-`q` offset below `P`.  The finite suffix-length bound is
then supplied by `TaoSection7Case3SourcePathData.coverage`.
-/
theorem taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_coverage
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
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfirst_source :
      ∀ first : ℕ,
        q < first →
          first < P →
            pointAt first =
              (taoSection7SourceHitPathPoint j s pre pres
                (first - q)).toPoint) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt A threshold P q pres.length old Γ candidate ∧
        ∃ first Γ',
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt j s pre pres P q old Γ' candidate first := by
  rcases
      taoSection7Case3_exists_activeBlackPivotStepInLaterWindow_of_sourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hlow hroom hactive hcover with
    ⟨candidate, Γ, hstep⟩
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_activeBlackPivotStepInLaterWindow_coverage
      hcover hstep hdata.coverage hfirst_source with
    ⟨first, Γ', hfirstProv⟩
  exact ⟨candidate, Γ, hstep, first, Γ', hfirstProv⟩

/--
Generic-scale source-data wrapper for first-hit provenance.

This is the checked stopping socket for the source-pivot route before the
outer strict-advance producer: it consumes the base-aware/generic source data
and returns a later-window active black pivot plus minimized first-hit source
provenance under the same `bound/gapBound`.
-/
theorem taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_scale_coverage
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
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfirst_source :
      ∀ first : ℕ,
        q < first →
          first < P →
            pointAt first =
              (taoSection7SourceHitPathPoint j s pre pres
                (first - q)).toPoint) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindowWithBound
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt bound gapBound threshold P q pres.length
        old Γ candidate ∧
        ∃ first Γ',
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt j s pre pres P q old Γ' candidate first := by
  rcases
      taoSection7Case3_exists_activeBlackPivotStepInLaterWindow_of_sourcePathData_scale
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive hcover with
    ⟨candidate, Γ, hstep⟩
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_activeBlackPivotStepInLaterWindowWithBound_coverage
        hcover hstep hdata.coverage hfirst_source with
    ⟨first, Γ', hfirstProv⟩
  exact ⟨candidate, Γ, hstep, first, Γ', hfirstProv⟩

/--
Start-based strict-advance socket from generic first-hit source provenance plus
explicit start-step/budget compatibility.

This is still not the final `hadvance` producer: the caller must prove the
actual recurrence step and budget for the minimized first hit.
-/
theorem taoSection7Case3_exists_strictBoundedAdvance_of_sourcePathData_scale_coverage_startStepBudget
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (Accepts :
      ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {bound : ℕ → ℝ} {gapBound B : ℕ → ℕ}
    {Step : ℕ → ℕ → Prop}
    {P start threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hq : q ∈ Finset.Icc start (start + threshold))
    (hdata :
      TaoSection7Case3SourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfirst_source :
      ∀ first : ℕ,
        q < first →
          first < P →
            pointAt first =
              (taoSection7SourceHitPathPoint j s pre pres
                (first - q)).toPoint)
    (haccept :
      ∀ candidate first Γ,
        TaoSection7Case3FirstHitSourceProvenance
          (taoSection7SourceBlackInDomain n xi epsilon J)
          family pointAt j s pre pres P q old Γ candidate first →
        Accepts q old first Γ)
    (hcompat :
      ∀ candidate first Γ,
        TaoSection7Case3FirstHitSourceProvenance
          (taoSection7SourceBlackInDomain n xi epsilon J)
          family pointAt j s pre pres P q old Γ candidate first →
        Accepts q old first Γ →
        Step start first ∧ first ≤ B start) :
    ∃ next : ℕ,
      taoSection7Case3StrictBoundedAdvance B Step start next := by
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_scale_coverage
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive hcover hfirst_source with
    ⟨candidate, _candidateΓ, _hwindow, first, Γ, hsrc⟩
  have haccepted : Accepts q old first Γ :=
    haccept candidate first Γ hsrc
  have hacc :
      TaoSection7Case3FirstHitAcceptedTransition
        (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt Accepts q old Γ first :=
    ⟨hsrc.first_hit, hsrc.first_black, hsrc.new_mem_family,
      hsrc.new_mem, hsrc.new_ne_old, haccepted⟩
  rcases hcompat candidate first Γ hsrc haccepted with ⟨hstep, hbound⟩
  exact
    taoSection7Case3_strictBoundedAdvance_of_firstHitAcceptedTransition
      hq hacc hstep hbound

/--
The later-search right endpoint controls the minimized first hit whenever the
producing candidate lies in the later-search window.

This is only budget arithmetic; it does not choose the recurrence relation
`Step`.
-/
theorem taoSection7Case3_first_le_startBudget_of_laterWindow_rightBound
    {B gapBound : ℕ → ℕ} {start threshold q candidate first : ℕ}
    (hmono : Monotone gapBound)
    (hq : q ∈ Finset.Icc start (start + threshold))
    (hmem :
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold))
    (hfirst : first ≤ candidate)
    (hright :
      taoSection7Case3LaterSearchBound gapBound threshold
          (start + threshold) ≤ B start) :
    first ≤ B start := by
  have hcandidate_le :
      candidate ≤ taoSection7Case3LaterSearchBound gapBound threshold q := by
    simpa [taoSection7Case3LaterSearchBound] using
      (Finset.mem_Icc.mp hmem).2
  exact
    hfirst.trans
      (hcandidate_le.trans
        ((taoSection7Case3_laterSearchBound_le_right_of_mem_window
            hmono hq).trans hright))

/--
Producer-facing source-path data with full post-`q` point equality on the
whole `P` window.

The current production `TaoSection7Case3SourcePathData` only asks for point
equality on the later-search block.  This stronger package is the shape needed
if the minimized q-relative first hit may occur before that block but still
needs to be used as a source-path rebase point.
-/
structure TaoSection7Case3FullWindowSourcePathData
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    (n J A : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P threshold q : ℕ)
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ)) : Prop where
  coverage : taoSection7SourceSuffixCoversWindow q P pres
  point_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint
  point_window :
    ∀ t : ℕ,
      q < t →
        t < P →
          pointAt t =
            (taoSection7SourceHitPathPoint j s pre pres (t - q)).toPoint
  white_iff_later :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      (W candidate ↔
        taoSection7SourceWhitePoint n xi epsilon (pointAt candidate))
  domain_later :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) q + threshold) →
      taoSection7SourcePointInDomain J (pointAt candidate)

/--
Generic-gap full-window source-path data for the stateful Case 3 recurrence
route.

This is the full-window analogue of `TaoSection7Case3SourcePathDataWithGap`;
it keeps enough point equality to rebase at the minimized first hit, while the
later-search color/domain facts use the caller-supplied `gapBound`.
-/
structure TaoSection7Case3FullWindowSourcePathDataWithGap
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    (n J : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P threshold q : ℕ) (gapBound : ℕ → ℕ)
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ)) : Prop where
  coverage : taoSection7SourceSuffixCoversWindow q P pres
  point_q : pointAt q = (taoSection7SourceHitPoint j s pre).toPoint
  point_window :
    ∀ t : ℕ,
      q < t →
        t < P →
          pointAt t =
            (taoSection7SourceHitPathPoint j s pre pres (t - q)).toPoint
  white_iff_later :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) →
      (W candidate ↔
        taoSection7SourceWhitePoint n xi epsilon (pointAt candidate))
  domain_later :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) →
      taoSection7SourcePointInDomain J (pointAt candidate)

theorem TaoSection7Case3FullWindowSourcePathData.to_sourcePathData
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q) :
    TaoSection7Case3SourcePathData
      W pointAt n J A xi epsilon P threshold q j s pre pres := by
  refine
    { coverage := hfull.coverage
      point_q := hfull.point_q
      point_candidate := ?_
      white_iff := hfull.white_iff_later
      domain := hfull.domain_later }
  intro candidate hcandidate
  have hstrict_ltP :
      taoSection7Case3HeightExitBound
          (taoSection7Case3ExitGapBound A) q < candidate ∧
        candidate < P :=
    taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
      hroom hcandidate
  have hq_candidate : q < candidate := by
    dsimp [taoSection7Case3HeightExitBound] at hstrict_ltP
    omega
  exact hfull.point_window candidate hq_candidate hstrict_ltP.2

theorem TaoSection7Case3FullWindowSourcePathDataWithGap.to_sourcePathDataWithGap
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ} {gapBound : ℕ → ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q) :
    TaoSection7Case3SourcePathDataWithGap
      W pointAt n J xi epsilon P threshold q gapBound j s pre pres := by
  refine
    { coverage := hfull.coverage
      point_q := hfull.point_q
      point_candidate := ?_
      white_iff := hfull.white_iff_later
      domain := hfull.domain_later }
  intro candidate hcandidate
  have hstrict_ltP :
      taoSection7Case3HeightExitBound gapBound q < candidate ∧
        candidate < P :=
    taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
      hroom hcandidate
  have hq_candidate : q < candidate := by
    dsimp [taoSection7Case3HeightExitBound] at hstrict_ltP
    omega
  exact hfull.point_window candidate hq_candidate hstrict_ltP.2

/-- Current horizontal scale for Lemma 7.10 at a Section 7 point. -/
def taoSection7Lemma710CurrentM (n : ℕ) (p : TaoSection7Point) : ℝ :=
  ((n / 2 - (p.j : ℕ) : ℕ) : ℝ)

/-- Nat-subtraction nontruncation for Tao's current horizontal scale. -/
theorem taoSection7Lemma710CurrentMNat_add_currentJ_eq_cutoff
    {cutoff : ℕ} {p : TaoSection7Point}
    (hp : taoSection7SourcePointInDomain cutoff p) :
    (p.j : ℕ) + (cutoff - (p.j : ℕ)) = cutoff :=
  Nat.add_sub_of_le hp

/-- Real form of the nontruncation identity for `taoSection7Lemma710CurrentM`. -/
theorem taoSection7Lemma710CurrentM_add_currentJ_eq_cutoff
    {n : ℕ} {p : TaoSection7Point}
    (hp : taoSection7SourcePointInDomain (n / 2) p) :
    ((p.j : ℕ) : ℝ) + taoSection7Lemma710CurrentM n p = ((n / 2 : ℕ) : ℝ) := by
  unfold taoSection7Lemma710CurrentM
  exact_mod_cast taoSection7Lemma710CurrentMNat_add_currentJ_eq_cutoff hp

/--
Current-`m` wrapper for Tao's `(7.52)` height bound from a named real
right-edge strip hypothesis.
-/
theorem taoSection7Lemma710_verticalDepth_le_log9_div_log2_mul_currentM_of_domain
    {n : ℕ} {old : TaoSection7Triangle} {p : TaoSection7Point}
    (hmem : old.Mem p)
    (hdomain : taoSection7SourcePointInDomain (n / 2) p)
    (hright :
      TaoSection7TriangleRightEdgeInStrip ((n / 2 : ℕ) : ℝ) old) :
    ((old.verticalDepth p : ℤ) : ℝ) ≤
      (Real.log 9 / Real.log 2) * taoSection7Lemma710CurrentM n p := by
  refine
    TaoSection7Triangle.verticalDepth_le_log9_div_log2_mul_rightGap_of_mem_rightEdge
      (old := old) (p := p) (S := ((old.verticalDepth p : ℤ) : ℝ))
      (M := taoSection7Lemma710CurrentM n p) (cutoff := ((n / 2 : ℕ) : ℝ))
      hmem rfl hright ?_
  unfold taoSection7Lemma710CurrentM
  dsimp [TaoSection7Point.jReal]
  rw [Nat.cast_sub hdomain]

/-- Active-triangle form of the `(7.52)` right-edge current-`m` bound. -/
theorem taoSection7Lemma710_verticalDepth_le_log9_div_log2_mul_currentM_of_active_rightEdge
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {n A q : ℕ} {old : TaoSection7Triangle}
    (hactive : TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hqdom : taoSection7SourcePointInDomain (n / 2) (pointAt q))
    (hright :
      TaoSection7TriangleFamilyRightEdgeInStrip ((n / 2 : ℕ) : ℝ) family) :
    ((old.verticalDepth (pointAt q) : ℤ) : ℝ) ≤
      (Real.log 9 / Real.log 2) * taoSection7Lemma710CurrentM n (pointAt q) :=
  taoSection7Lemma710_verticalDepth_le_log9_div_log2_mul_currentM_of_domain
    hactive.pivot_mem hqdom
    (TaoSection7Case3ActiveTriangleAt.rightEdgeInStrip hactive hright)

/--
Current source-scale controls for Tao Lemma 7.10.

This packages the current gap `M = floor(n/2)-j`, the old crossing height `S`,
the log-domain/lower-scale hypotheses supplied by later source work, and the
checked `(7.52)` upper scale bound.  It is not endpoint production.
-/
structure TaoSection7Lemma710CurrentScaleControls
    (n : ℕ) (old : TaoSection7Triangle) (p : TaoSection7Point)
    (M S : ℝ) : Prop where
  M_def : M = taoSection7Lemma710CurrentM n p
  S_def : S = ((old.verticalDepth p : ℤ) : ℝ)
  domain : taoSection7SourcePointInDomain (n / 2) p
  M_large : 1 < M
  logM_pos : 0 < Real.log M
  S_nonneg : 0 ≤ S
  hMlower : M / (Real.log M)^2 ≤ S
  upper_752 : S ≤ (Real.log 9 / Real.log 2) * M

theorem taoSection7Lemma710CurrentScaleControls_of_domain_rightEdge
    {n : ℕ} {old : TaoSection7Triangle} {p : TaoSection7Point}
    {M S : ℝ}
    (hmem : old.Mem p)
    (hdomain : taoSection7SourcePointInDomain (n / 2) p)
    (hright :
      TaoSection7TriangleRightEdgeInStrip ((n / 2 : ℕ) : ℝ) old)
    (hM : M = taoSection7Lemma710CurrentM n p)
    (hS : S = ((old.verticalDepth p : ℤ) : ℝ))
    (hMlarge : 1 < M)
    (hMlower : M / (Real.log M)^2 ≤ S) :
    TaoSection7Lemma710CurrentScaleControls n old p M S := by
  refine
    { M_def := hM
      S_def := hS
      domain := hdomain
      M_large := hMlarge
      logM_pos := Real.log_pos hMlarge
      S_nonneg := ?_
      hMlower := hMlower
      upper_752 := ?_ }
  · rw [hS]
    exact_mod_cast TaoSection7Triangle.verticalDepth_nonneg_of_mem hmem
  · rw [hS, hM]
    exact
      taoSection7Lemma710_verticalDepth_le_log9_div_log2_mul_currentM_of_domain
        hmem hdomain hright

theorem taoSection7Lemma710CurrentScaleControls_of_active_rightEdge
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {n A q : ℕ} {old : TaoSection7Triangle} {M S : ℝ}
    (hactive : TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hqdom : taoSection7SourcePointInDomain (n / 2) (pointAt q))
    (hright :
      TaoSection7TriangleFamilyRightEdgeInStrip ((n / 2 : ℕ) : ℝ) family)
    (hM : M = taoSection7Lemma710CurrentM n (pointAt q))
    (hS : S = ((old.verticalDepth (pointAt q) : ℤ) : ℝ))
    (hMlarge : 1 < M)
    (hMlower : M / (Real.log M)^2 ≤ S) :
    TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S :=
  taoSection7Lemma710CurrentScaleControls_of_domain_rightEdge
    hactive.pivot_mem hqdom
    (TaoSection7Case3ActiveTriangleAt.rightEdgeInStrip hactive hright)
    hM hS hMlarge hMlower

namespace TaoSection7Lemma710CurrentScaleControls

/-- Consume the current-scale ledger to convert an `S^(3/5)` horizontal error to `(C*M)^(3/5)`. -/
theorem jerr_le_log9_div_log2_mul_currentM_rpow
    {n : ℕ} {old : TaoSection7Triangle} {p : TaoSection7Point}
    {M S Jerr CJ : ℝ}
    (hscale : TaoSection7Lemma710CurrentScaleControls n old p M S)
    (hCJ0 : 0 ≤ CJ)
    (hJ : Jerr ≤ CJ * S ^ (3 / 5 : ℝ)) :
    Jerr ≤ CJ * ((Real.log 9 / Real.log 2) * M) ^ (3 / 5 : ℝ) :=
  TaoSection7Lemma710.jerr_mpow_of_s_rpow_bound_of_upper752
    hscale.S_nonneg hCJ0 hscale.upper_752 hJ

/--
Consumer form that leaves the constant absorption from
`((log 9 / log 2) * M)^(3/5)` to `M^(3/5)` explicit.
-/
theorem jerr_le_mpow_of_s_rpow_bound_absorb
    {n : ℕ} {old : TaoSection7Triangle} {p : TaoSection7Point}
    {M S Jerr CJ CJm : ℝ}
    (hscale : TaoSection7Lemma710CurrentScaleControls n old p M S)
    (hCJ0 : 0 ≤ CJ)
    (hJ : Jerr ≤ CJ * S ^ (3 / 5 : ℝ))
    (habsorb :
      CJ * ((Real.log 9 / Real.log 2) * M) ^ (3 / 5 : ℝ) ≤
        CJm * M ^ (3 / 5 : ℝ)) :
    Jerr ≤ CJm * M ^ (3 / 5 : ℝ) :=
  le_trans
    (hscale.jerr_le_log9_div_log2_mul_currentM_rpow hCJ0 hJ)
    habsorb

/--
Current-scale consumer for the scalar row-margin premise.  The horizontal
estimate may be supplied in the old-height scale `S`; the conversion to an
`M^(3/5)` bound and final large-`m` absorption remain explicit.
-/
theorem error_margin_of_s_rpow_bound_absorb
    {n : ℕ} {old : TaoSection7Triangle} {p : TaoSection7Point}
    {M S B Lerr Jerr CJS CJm CL CB : ℝ}
    (hscale : TaoSection7Lemma710CurrentScaleControls n old p M S)
    (hCL_nonneg : 0 ≤ CL)
    (hCJS_nonneg : 0 ≤ CJS)
    (hJ : Jerr ≤ CJS * S ^ (3 / 5 : ℝ))
    (hJabsorb :
      CJS * ((Real.log 9 / Real.log 2) * M) ^ (3 / 5 : ℝ) ≤
        CJm * M ^ (3 / 5 : ℝ))
    (hL : Lerr ≤ CL * B)
    (hB : B ≤ CB * M ^ (3 / 5 : ℝ))
    (habsorb :
      CJm * M ^ (3 / 5 : ℝ) +
          (Real.log 2 / Real.log 9) * (CL * CB * M ^ (3 / 5 : ℝ)) + 1 ≤
        (M / (Real.log M)^2) *
          (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))) :
    Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
      S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) := by
  have hJ_m :
      Jerr ≤ CJm * M ^ (3 / 5 : ℝ) :=
    hscale.jerr_le_mpow_of_s_rpow_bound_absorb
      hCJS_nonneg hJ hJabsorb
  exact
    TaoSection7Lemma710.lemma710_error_margin_of_sourceScale
      hCL_nonneg hscale.hMlower hJ_m hL hB habsorb

end TaoSection7Lemma710CurrentScaleControls

/-- The full-window source package identifies the pivot index with the shifted source index. -/
theorem TaoSection7Case3FullWindowSourcePathData.point_q_j_eq
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres) :
    (pointAt q).j = taoSection7ShiftIndex j pre.length := by
  have h := congrArg TaoSection7Point.j hfull.point_q
  simpa [taoSection7SourceHitPoint, TaoSection7RenewalPoint.toPoint] using h

/-- Current horizontal scale `m = floor(n/2) - j` using the shifted pivot index. -/
theorem TaoSection7Case3FullWindowSourcePathData.currentM_eq_shifted
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres) :
    n / 2 - ((pointAt q).j : ℕ) =
      n / 2 - ((taoSection7ShiftIndex j pre.length : ℕ+) : ℕ) := by
  rw [TaoSection7Case3FullWindowSourcePathData.point_q_j_eq hfull]

/--
The source-domain guard identifies the shifted pivot index as a nontruncated
source index below the current cutoff `n / 2`.
-/
theorem TaoSection7Case3FullWindowSourcePathData.shiftedIndex_le_cutoff
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n A P threshold q : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n (n / 2) A xi epsilon P threshold q j s pre pres)
    (hqdom : taoSection7SourcePointInDomain (n / 2) (pointAt q)) :
    ((taoSection7ShiftIndex j pre.length : ℕ+) : ℕ) ≤ n / 2 := by
  simpa [taoSection7SourcePointInDomain,
    TaoSection7Case3FullWindowSourcePathData.point_q_j_eq hfull] using hqdom

/-- Shifted-index form of the current-scale Nat nontruncation identity. -/
theorem TaoSection7Case3FullWindowSourcePathData.shiftedIndex_add_currentM_eq_cutoff
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n A P threshold q : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n (n / 2) A xi epsilon P threshold q j s pre pres)
    (hqdom : taoSection7SourcePointInDomain (n / 2) (pointAt q)) :
    ((taoSection7ShiftIndex j pre.length : ℕ+) : ℕ) +
        (n / 2 - ((taoSection7ShiftIndex j pre.length : ℕ+) : ℕ)) = n / 2 :=
  Nat.add_sub_of_le
    (TaoSection7Case3FullWindowSourcePathData.shiftedIndex_le_cutoff hfull hqdom)

/-- The full-window source package identifies the pivot height with the source hit height. -/
theorem TaoSection7Case3FullWindowSourcePathData.point_q_l_eq
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres) :
    (pointAt q).l = Int.ofNat (s + pre.sum + 3) := by
  have h := congrArg TaoSection7Point.l hfull.point_q
  simpa [taoSection7SourceHitPoint, TaoSection7RenewalPoint.toPoint] using h

/--
Source-height adapter for the old crossing height used by Lemma 7.10's
row-control margin.  This is only an identity; scale lower bounds remain a
separate source obligation.
-/
theorem TaoSection7Case3FullWindowSourcePathData.oldCrossingHeight_eq
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres) :
    ((old.cornerL - (pointAt q).l : ℤ) : ℝ) =
      ((old.cornerL - Int.ofNat (s + pre.sum + 3) : ℤ) : ℝ) := by
  have hq_l : (pointAt q).l = Int.ofNat (s + pre.sum + 3) :=
    TaoSection7Case3FullWindowSourcePathData.point_q_l_eq hfull
  simp [hq_l]

/-- Real-subtraction form of `oldCrossingHeight_eq` for later scale estimates. -/
theorem TaoSection7Case3FullWindowSourcePathData.oldCrossingHeight_realSub_eq
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres) :
    ((old.cornerL - (pointAt q).l : ℤ) : ℝ) =
      (old.cornerL : ℝ) - ((s + pre.sum + 3 : ℕ) : ℝ) := by
  rw [TaoSection7Case3FullWindowSourcePathData.oldCrossingHeight_eq hfull]
  rw [Int.cast_sub]
  congr 1

/-- Split a suffix list at a positive one-based offset. -/
theorem taoSection7Case3_exists_sourceSuffix_split_at_positive_offset
    {α : Type*} (xs : List α) {d : ℕ}
    (hpos : 0 < d) (hle : d ≤ xs.length) :
    ∃ before x after,
      xs = before ++ x :: after ∧ before.length + 1 = d := by
  cases d with
  | zero =>
      omega
  | succ k =>
      have hk : k < xs.length := by omega
      refine ⟨xs.take k, xs[k], xs.drop (k + 1), ?_, ?_⟩
      · calc
          xs = xs.take k ++ xs.drop k := by
            rw [List.take_append_drop]
          _ = xs.take k ++ xs[k] :: xs.drop (k + 1) := by
            rw [← List.cons_getElem_drop_succ (l := xs) (n := k) (h := hk)]
      · have htake : (xs.take k).length = k := by
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
        omega

theorem taoSection7Case3_exists_sourceSuffix_split_at_firstHit
    {α : Type*} (xs : List α) {q first : ℕ}
    (hq_first : q < first) (hfirst_len : first - q ≤ xs.length) :
    ∃ before x after,
      xs = before ++ x :: after ∧ before.length + 1 = first - q := by
  exact
    taoSection7Case3_exists_sourceSuffix_split_at_positive_offset xs
      (by omega) hfirst_len

theorem taoSection7Case3_sourceSuffixCoversWindow_rebase
    {q first P : ℕ} {pres before after : List (List ℕ)}
    {next : List ℕ}
    (hcoverage : taoSection7SourceSuffixCoversWindow q P pres)
    (hsplit : pres = before ++ next :: after)
    (hidx : before.length + 1 = first - q)
    (hq_first : q < first) :
    taoSection7SourceSuffixCoversWindow first P after := by
  rw [taoSection7SourceSuffixCoversWindow] at hcoverage ⊢
  rw [hsplit] at hcoverage
  simp at hcoverage
  omega

theorem taoSection7Case3_sourceHitPathPoint_rebase_at_split
    (j : ℕ+) (s : ℕ) (pre : List ℕ)
    {pres before after : List (List ℕ)} {next : List ℕ}
    {q first : ℕ}
    (hsplit : pres = before ++ next :: after)
    (hidx : before.length + 1 = first - q) :
    taoSection7SourceHitPathPoint j s pre pres (first - q) =
      taoSection7SourceHitPoint
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before)) next := by
  rw [hsplit, ← hidx]
  exact
    taoSection7SourceHitPathPoint_after_prefix
      (j := j) (s := s) (first := pre)
      (before := before) (pre := next) (pres := after)

theorem taoSection7Case3_sourceHitPathPoint_rebase_after_split
    (j : ℕ+) (s : ℕ) (pre : List ℕ)
    {pres before after : List (List ℕ)} {next : List ℕ}
    {q first t : ℕ}
    (hsplit : pres = before ++ next :: after)
    (hidx : before.length + 1 = first - q)
    (hq_first : q < first)
    (hfirst_t : first < t) :
    taoSection7SourceHitPathPoint j s pre pres (t - q) =
      taoSection7SourceHitPathPoint
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before))
        next after (t - first) := by
  rw [hsplit]
  have htq :
      t - q = before.length + (t - first) + 1 := by
    omega
  rw [htq]
  exact
    taoSection7SourceHitPathPoint_after_prefix_add
      (j := j) (s := s) (first := pre)
      (before := before) (pre := next) (pres := after)
      (n := t - first)

theorem taoSection7Case3_pointAt_rebase_first
    (pointAt : ℕ → TaoSection7Point)
    {j : ℕ+} {s : ℕ} {pre : List ℕ}
    {pres before after : List (List ℕ)} {next : List ℕ}
    {q first : ℕ}
    (hfirst_source :
      pointAt first =
        (taoSection7SourceHitPathPoint j s pre pres (first - q)).toPoint)
    (hsplit : pres = before ++ next :: after)
    (hidx : before.length + 1 = first - q) :
    pointAt first =
      (taoSection7SourceHitPoint
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before)) next).toPoint := by
  calc
    pointAt first =
        (taoSection7SourceHitPathPoint j s pre pres (first - q)).toPoint :=
      hfirst_source
    _ =
        (taoSection7SourceHitPoint
          (taoSection7SourceBlockStartJFrom j (pre :: before))
          (taoSection7SourceBlockStartSFrom s (pre :: before)) next).toPoint := by
      rw [taoSection7Case3_sourceHitPathPoint_rebase_at_split
        (j := j) (s := s) (pre := pre) hsplit hidx]

theorem taoSection7Case3_pointAt_rebase_window
    (pointAt : ℕ → TaoSection7Point)
    {j : ℕ+} {s : ℕ} {pre : List ℕ}
    {pres before after : List (List ℕ)} {next : List ℕ}
    {P q first : ℕ}
    (hpoint_window :
      ∀ t : ℕ, q < t → t < P →
        pointAt t =
          (taoSection7SourceHitPathPoint j s pre pres (t - q)).toPoint)
    (hsplit : pres = before ++ next :: after)
    (hidx : before.length + 1 = first - q)
    (hq_first : q < first) :
    ∀ t : ℕ, first < t → t < P →
      pointAt t =
        (taoSection7SourceHitPathPoint
          (taoSection7SourceBlockStartJFrom j (pre :: before))
          (taoSection7SourceBlockStartSFrom s (pre :: before))
          next after (t - first)).toPoint := by
  intro t hfirst_t htP
  have hq_t : q < t := by omega
  calc
    pointAt t =
        (taoSection7SourceHitPathPoint j s pre pres (t - q)).toPoint :=
      hpoint_window t hq_t htP
    _ =
        (taoSection7SourceHitPathPoint
          (taoSection7SourceBlockStartJFrom j (pre :: before))
          (taoSection7SourceBlockStartSFrom s (pre :: before))
          next after (t - first)).toPoint := by
      rw [taoSection7Case3_sourceHitPathPoint_rebase_after_split
        (j := j) (s := s) (pre := pre) hsplit hidx hq_first hfirst_t]

theorem taoSection7Case3_fullWindowSourcePathData_rebase_of_split
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first : ℕ}
    {j : ℕ+} {s : ℕ} {pre next : List ℕ}
    {pres before after : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hsplit : pres = before ++ next :: after)
    (hidx : before.length + 1 = first - q)
    (hq_first : q < first)
    (hfirst_ltP : first < P)
    (hwhite_new :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) first)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) first + threshold) →
        (W candidate ↔
          taoSection7SourceWhitePoint n xi epsilon (pointAt candidate)))
    (hdomain_new :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) first)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) first + threshold) →
        taoSection7SourcePointInDomain J (pointAt candidate)) :
    TaoSection7Case3FullWindowSourcePathData
      W pointAt n J A xi epsilon P threshold first
      (taoSection7SourceBlockStartJFrom j (pre :: before))
      (taoSection7SourceBlockStartSFrom s (pre :: before))
      next after := by
  refine
    { coverage := ?_
      point_q := ?_
      point_window := ?_
      white_iff_later := hwhite_new
      domain_later := hdomain_new }
  · exact
      taoSection7Case3_sourceSuffixCoversWindow_rebase
        hfull.coverage hsplit hidx hq_first
  · exact
      taoSection7Case3_pointAt_rebase_first
        pointAt (hfull.point_window first hq_first hfirst_ltP)
        hsplit hidx
  · exact
      taoSection7Case3_pointAt_rebase_window pointAt hfull.point_window
        hsplit hidx hq_first

theorem taoSection7Case3_fullWindowSourcePathDataWithGap_rebase_of_split
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first : ℕ} {gapBound : ℕ → ℕ}
    {j : ℕ+} {s : ℕ} {pre next : List ℕ}
    {pres before after : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hsplit : pres = before ++ next :: after)
    (hidx : before.length + 1 = first - q)
    (hq_first : q < first)
    (hfirst_ltP : first < P)
    (hwhite_new :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart gapBound first)
          (taoSection7Case3LaterSearchStart gapBound first + threshold) →
        (W candidate ↔
          taoSection7SourceWhitePoint n xi epsilon (pointAt candidate)))
    (hdomain_new :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart gapBound first)
          (taoSection7Case3LaterSearchStart gapBound first + threshold) →
        taoSection7SourcePointInDomain J (pointAt candidate)) :
    TaoSection7Case3FullWindowSourcePathDataWithGap
      W pointAt n J xi epsilon P threshold first gapBound
      (taoSection7SourceBlockStartJFrom j (pre :: before))
      (taoSection7SourceBlockStartSFrom s (pre :: before))
      next after := by
  refine
    { coverage := ?_
      point_q := ?_
      point_window := ?_
      white_iff_later := hwhite_new
      domain_later := hdomain_new }
  · exact
      taoSection7Case3_sourceSuffixCoversWindow_rebase
        hfull.coverage hsplit hidx hq_first
  · exact
      taoSection7Case3_pointAt_rebase_first
        pointAt (hfull.point_window first hq_first hfirst_ltP)
        hsplit hidx
  · exact
      taoSection7Case3_pointAt_rebase_window pointAt hfull.point_window
        hsplit hidx hq_first

theorem taoSection7Case3_exists_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first candidate : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ}
    {pres : List (List ℕ)} {old Γ : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hwhite_new :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) first)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) first + threshold) →
        (W candidate ↔
          taoSection7SourceWhitePoint n xi epsilon (pointAt candidate)))
    (hdomain_new :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) first)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) first + threshold) →
        taoSection7SourcePointInDomain J (pointAt candidate)) :
    ∃ before : List (List ℕ), ∃ next : List ℕ, ∃ after : List (List ℕ),
      pres = before ++ next :: after ∧
      before.length + 1 = first - q ∧
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold first
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before))
        next after := by
  have hq_first : q < first := hsrc.first_hit.1
  rcases
      taoSection7Case3_exists_sourceSuffix_split_at_firstHit
        pres hq_first hsrc.first_source_length with
    ⟨before, next, after, hsplit, hidx⟩
  refine ⟨before, next, after, hsplit, hidx, ?_⟩
  exact
    taoSection7Case3_fullWindowSourcePathData_rebase_of_split
      (hfull := hfull) hsplit hidx hq_first hsrc.first_ltP
      hwhite_new hdomain_new

theorem taoSection7Case3_exists_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first candidate : ℕ} {gapBound : ℕ → ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ}
    {pres : List (List ℕ)} {old Γ : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hwhite_new :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart gapBound first)
          (taoSection7Case3LaterSearchStart gapBound first + threshold) →
        (W candidate ↔
          taoSection7SourceWhitePoint n xi epsilon (pointAt candidate)))
    (hdomain_new :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart gapBound first)
          (taoSection7Case3LaterSearchStart gapBound first + threshold) →
        taoSection7SourcePointInDomain J (pointAt candidate)) :
    ∃ before : List (List ℕ), ∃ next : List ℕ, ∃ after : List (List ℕ),
      pres = before ++ next :: after ∧
      before.length + 1 = first - q ∧
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold first gapBound
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before))
        next after := by
  have hq_first : q < first := hsrc.first_hit.1
  rcases
      taoSection7Case3_exists_sourceSuffix_split_at_firstHit
        pres hq_first hsrc.first_source_length with
    ⟨before, next, after, hsplit, hidx⟩
  refine ⟨before, next, after, hsplit, hidx, ?_⟩
  exact
    taoSection7Case3_fullWindowSourcePathDataWithGap_rebase_of_split
      (hfull := hfull) hsplit hidx hq_first hsrc.first_ltP
      hwhite_new hdomain_new

theorem taoSection7Case3_exists_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance_allWindowFacts
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first candidate : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ}
    {pres : List (List ℕ)} {old Γ : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P first)
    (hwhite_all :
      ∀ t : ℕ, t < P →
        (W t ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt t)))
    (hdomain_all :
      ∀ t : ℕ, t < P →
        taoSection7SourcePointInDomain J (pointAt t)) :
    ∃ before : List (List ℕ), ∃ next : List ℕ, ∃ after : List (List ℕ),
      pres = before ++ next :: after ∧
      before.length + 1 = first - q ∧
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold first
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before))
        next after := by
  refine
    taoSection7Case3_exists_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance
      (hfull := hfull) (hsrc := hsrc) ?_ ?_
  · intro t ht
    exact hwhite_all t
      (taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom_first ht).2
  · intro t ht
    exact hdomain_all t
      (taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom_first ht).2

theorem taoSection7Case3_exists_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance_allWindowFacts
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first candidate : ℕ} {gapBound : ℕ → ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ}
    {pres : List (List ℕ)} {old Γ : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hwhite_all :
      ∀ t : ℕ, t < P →
        (W t ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt t)))
    (hdomain_all :
      ∀ t : ℕ, t < P →
        taoSection7SourcePointInDomain J (pointAt t)) :
    ∃ before : List (List ℕ), ∃ next : List ℕ, ∃ after : List (List ℕ),
      pres = before ++ next :: after ∧
      before.length + 1 = first - q ∧
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold first gapBound
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before))
        next after := by
  refine
    taoSection7Case3_exists_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
      (hfull := hfull) (hsrc := hsrc) ?_ ?_
  · intro t ht
    exact hwhite_all t
      (taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom_first ht).2
  · intro t ht
    exact hdomain_all t
      (taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom_first ht).2

/--
Source facts available on the whole finite `P` window.

This is a support token for rebasing after a first hit.  It does not produce
the facts from the source process or from Tao's recursion.
-/
structure TaoSection7Case3AllWindowSourceFacts
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    (n J : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (P : ℕ) : Prop where
  white_all :
    ∀ t : ℕ, t < P →
      (W t ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt t))
  domain_all :
    ∀ t : ℕ, t < P →
      taoSection7SourcePointInDomain J (pointAt t)

theorem taoSection7Case3_allWindowSourceFacts_of_sourceCutoffPoint_alignment
    (W : ℕ → Prop) (pointAt : ℕ → TaoSection7Point)
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (halign :
      ∀ t : ℕ, t < P →
        (W t ↔ taoSection7Case3SourceCutoffPointW pointAt n xi epsilon J t))
    (hdomain :
      ∀ t : ℕ, t < P →
        taoSection7SourcePointInDomain J (pointAt t)) :
    TaoSection7Case3AllWindowSourceFacts
      W pointAt n J xi epsilon P := by
  refine
    { white_all := ?_
      domain_all := hdomain }
  intro t htP
  exact
    taoSection7Case3_rawWhite_iff_of_sourceCutoffPoint_alignment
      W pointAt halign htP (hdomain t htP)

namespace TaoSection7Case3AllWindowSourceFacts

theorem white_iff_later
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A P threshold base : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P base) :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) base)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) base + threshold) →
      (W candidate ↔
        taoSection7SourceWhitePoint n xi epsilon (pointAt candidate)) := by
  intro candidate hcandidate
  exact hfacts.white_all candidate
    (taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
      hroom hcandidate).2

theorem domain_later
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A P threshold base : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P base) :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) base)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound A) base + threshold) →
      taoSection7SourcePointInDomain J (pointAt candidate) := by
  intro candidate hcandidate
  exact hfacts.domain_all candidate
    (taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
      hroom hcandidate).2

theorem white_iff_later_withGap
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J P threshold base : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {gapBound : ℕ → ℕ}
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P base) :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound base)
        (taoSection7Case3LaterSearchStart gapBound base + threshold) →
      (W candidate ↔
        taoSection7SourceWhitePoint n xi epsilon (pointAt candidate)) := by
  intro candidate hcandidate
  exact hfacts.white_all candidate
    (taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
      hroom hcandidate).2

theorem domain_later_withGap
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J P threshold base : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {gapBound : ℕ → ℕ}
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P base) :
    ∀ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound base)
        (taoSection7Case3LaterSearchStart gapBound base + threshold) →
      taoSection7SourcePointInDomain J (pointAt candidate) := by
  intro candidate hcandidate
  exact hfacts.domain_all candidate
    (taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
      hroom hcandidate).2

/-- Domain projection for the actual current q-point of the all-window source package. -/
theorem q_sourceDomain
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J P q : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hqP : q < P) :
    taoSection7SourcePointInDomain J (pointAt q) :=
  hfacts.domain_all q hqP

theorem blackInDomain_iff_sourceBlackPoint
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J P p : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hpP : p < P) :
    (taoSection7SourceBlackInDomain n xi epsilon J (pointAt p) ↔
      taoSection7SourceBlackPoint n xi epsilon (pointAt p)) := by
  constructor
  · intro hblack
    exact hblack.2
  · intro hblack
    exact ⟨hfacts.domain_all p hpP, hblack⟩

theorem positiveWhiteCount_eq_sourceWhitePoint_sum
    {W : ℕ → Prop} [DecidablePred W]
    {pointAt : ℕ → TaoSection7Point}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt p))]
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    {t : ℕ} (ht : t < P) :
    taoSection7Case3PositiveWhiteCount W t =
      (Finset.Icc 1 t).sum
        (fun p : ℕ =>
          if taoSection7SourceWhitePoint n xi epsilon (pointAt p) then
            1
          else
            0) := by
  unfold taoSection7Case3PositiveWhiteCount
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpP : p < P :=
    lt_of_le_of_lt (Finset.mem_Icc.1 hp).2 ht
  have hwhite :
      W p ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt p) :=
    hfacts.white_all p hpP
  by_cases hW : W p
  · have hsource :
        taoSection7SourceWhitePoint n xi epsilon (pointAt p) :=
      hwhite.mp hW
    simp [hW, hsource]
  · have hsource :
        ¬ taoSection7SourceWhitePoint n xi epsilon (pointAt p) := by
      intro hsource
      exact hW (hwhite.mpr hsource)
    simp [hW, hsource]

theorem threshold_lt_positiveWhiteCount_of_sourceWhitePoint_sum
    {W : ℕ → Prop} [DecidablePred W]
    {pointAt : ℕ → TaoSection7Point}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt p))]
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    {t threshold : ℕ} (ht : t < P)
    (hsource :
      threshold <
        (Finset.Icc 1 t).sum
          (fun p : ℕ =>
            if taoSection7SourceWhitePoint n xi epsilon (pointAt p) then
              1
            else
              0)) :
    threshold < taoSection7Case3PositiveWhiteCount W t := by
  rwa [hfacts.positiveWhiteCount_eq_sourceWhitePoint_sum ht]

end TaoSection7Case3AllWindowSourceFacts

theorem taoSection7Case3_exists_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance_allWindowPackage
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first candidate : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ}
    {pres : List (List ℕ)} {old Γ : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P) :
    ∃ before : List (List ℕ), ∃ next : List ℕ, ∃ after : List (List ℕ),
      pres = before ++ next :: after ∧
      before.length + 1 = first - q ∧
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold first
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before))
        next after := by
  exact
    taoSection7Case3_exists_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance
      (hfull := hfull) (hsrc := hsrc)
      (TaoSection7Case3AllWindowSourceFacts.white_iff_later
        hfacts hroom_first)
      (TaoSection7Case3AllWindowSourceFacts.domain_later
        hfacts hroom_first)

/--
Full-window source-path data feeds the existing later-black route and also
supplies the point equality needed by the q-relative minimized first hit.
-/
theorem taoSection7Case3_exists_firstHitSourceProvenance_of_fullWindowSourcePathData
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt A threshold P q pres.length old Γ candidate ∧
        ∃ first Γ',
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt j s pre pres P q old Γ' candidate first := by
  have hdata :
      TaoSection7Case3SourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres :=
    hfull.to_sourcePathData hroom
  exact
    taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_coverage
      (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
      (xi := xi) (epsilon := epsilon) (family := family) (old := old)
      (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
      (pre := pre) (pres := pres)
      hdata hlow hroom hactive hcover hfull.point_window

/--
Global-prefix producer-facing full-window source provenance.

This is the full-window analogue of
`TaoSection7Case3GlobalSourceSuffixProvenance`: it keeps the existing global
split coordinates, but strengthens `pointAt` equality from
`{q} ∪ laterSearchIcc` to every strict post-`q` offset below `P`.
-/
structure TaoSection7Case3GlobalFullWindowSourceSuffixProvenance
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
  point_q :
    pointAt q =
      (taoSection7SourceHitPoint
        (taoSection7SourceBlockStartJ before)
        (taoSection7SourceBlockStartS before) pre).toPoint
  pointAt_source_window :
    ∀ t : ℕ,
      q < t →
        t < P →
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

theorem TaoSection7Case3GlobalFullWindowSourceSuffixProvenance.to_fullWindowSourcePathData
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hglobal :
      TaoSection7Case3GlobalFullWindowSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q blocks before pre pres)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q) :
    TaoSection7Case3FullWindowSourcePathData
      W pointAt n J A xi epsilon P threshold q
      (taoSection7SourceBlockStartJ before)
      (taoSection7SourceBlockStartS before) pre pres := by
  refine
    { coverage := ?_
      point_q := hglobal.point_q
      point_window := hglobal.pointAt_source_window
      white_iff_later := ?_
      domain_later := ?_ }
  · exact
      taoSection7SourceSuffixCoversWindow_of_blockSplit
        hglobal.blocks_eq hglobal.q_eq hglobal.window_le
  · intro candidate hcandidate
    have hstrict_ltP :
        taoSection7Case3HeightExitBound
            (taoSection7Case3ExitGapBound A) q < candidate ∧
          candidate < P :=
      taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom hcandidate
    have hq_candidate : q < candidate := by
      dsimp [taoSection7Case3HeightExitBound] at hstrict_ltP
      omega
    have hpoint :
        pointAt candidate =
          (taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ before)
            (taoSection7SourceBlockStartS before)
            pre pres (candidate - q)).toPoint :=
      hglobal.pointAt_source_window candidate hq_candidate hstrict_ltP.2
    simpa [hpoint] using hglobal.white_iff_source candidate hcandidate
  · intro candidate hcandidate
    have hstrict_ltP :
        taoSection7Case3HeightExitBound
            (taoSection7Case3ExitGapBound A) q < candidate ∧
          candidate < P :=
      taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom hcandidate
    have hq_candidate : q < candidate := by
      dsimp [taoSection7Case3HeightExitBound] at hstrict_ltP
      omega
    have hpoint :
        pointAt candidate =
          (taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ before)
            (taoSection7SourceBlockStartS before)
            pre pres (candidate - q)).toPoint :=
      hglobal.pointAt_source_window candidate hq_candidate hstrict_ltP.2
    simpa [hpoint] using hglobal.domain_source candidate hcandidate

theorem TaoSection7Case3GlobalFullWindowSourceSuffixProvenance.to_globalSourceSuffixProvenance
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hglobal :
      TaoSection7Case3GlobalFullWindowSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q blocks before pre pres)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q) :
    TaoSection7Case3GlobalSourceSuffixProvenance
      W pointAt n J A xi epsilon P threshold q blocks before pre pres := by
  refine
    { blocks_eq := hglobal.blocks_eq
      q_eq := hglobal.q_eq
      window_le := hglobal.window_le
      noThree_before := hglobal.noThree_before
      noThree_pre := hglobal.noThree_pre
      noThree_pres := hglobal.noThree_pres
      pointAt_source := ?_
      white_iff_source := hglobal.white_iff_source
      domain_source := hglobal.domain_source }
  intro t ht
  rcases Finset.mem_insert.mp ht with htq | ht_later
  · subst t
    simpa using hglobal.point_q
  · have hstrict_ltP :
        taoSection7Case3HeightExitBound
            (taoSection7Case3ExitGapBound A) q < t ∧
          t < P :=
      taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom ht_later
    have hq_t : q < t := by
      dsimp [taoSection7Case3HeightExitBound] at hstrict_ltP
      omega
    exact hglobal.pointAt_source_window t hq_t hstrict_ltP.2

theorem taoSection7Case3_exists_firstHitSourceProvenance_of_globalFullWindowSourceSuffixProvenance
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {blocks before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hglobal :
      TaoSection7Case3GlobalFullWindowSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q blocks before pre pres)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt A threshold P q pres.length old Γ candidate ∧
        ∃ first Γ',
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt
              (taoSection7SourceBlockStartJ before)
              (taoSection7SourceBlockStartS before)
              pre pres P q old Γ' candidate first := by
  exact
    taoSection7Case3_exists_firstHitSourceProvenance_of_fullWindowSourcePathData
      (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
      (xi := xi) (epsilon := epsilon) (family := family) (old := old)
      (P := P) (threshold := threshold) (q := q)
      (j := taoSection7SourceBlockStartJ before)
      (s := taoSection7SourceBlockStartS before)
      (pre := pre) (pres := pres)
      (hglobal.to_fullWindowSourcePathData hroom)
      hlow hroom hactive hcover

/--
Distinguished-first producer-facing full-window source provenance.

This is the full-window analogue of
`TaoSection7Case3DistinguishedSourceSuffixProvenance`, using the
`first :: before` origin convention.
-/
structure TaoSection7Case3DistinguishedFullWindowSourceSuffixProvenance
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
  point_q :
    pointAt q =
      (taoSection7SourceHitPoint
        (taoSection7SourceBlockStartJ (first :: before))
        (taoSection7SourceBlockStartS (first :: before)) pre).toPoint
  pointAt_source_window :
    ∀ t : ℕ,
      q < t →
        t < P →
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

theorem TaoSection7Case3DistinguishedFullWindowSourceSuffixProvenance.to_fullWindowSourcePathData
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {first : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hsrc :
      TaoSection7Case3DistinguishedFullWindowSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q
        blocks first before pre pres)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q) :
    TaoSection7Case3FullWindowSourcePathData
      W pointAt n J A xi epsilon P threshold q
      (taoSection7SourceBlockStartJ (first :: before))
      (taoSection7SourceBlockStartS (first :: before)) pre pres := by
  refine
    { coverage := ?_
      point_q := hsrc.point_q
      point_window := hsrc.pointAt_source_window
      white_iff_later := ?_
      domain_later := ?_ }
  · exact
      taoSection7SourceSuffixCoversWindow_of_distinguishedBlockSplit
        hsrc.blocks_eq hsrc.q_eq hsrc.window_le
  · intro candidate hcandidate
    have hstrict_ltP :
        taoSection7Case3HeightExitBound
            (taoSection7Case3ExitGapBound A) q < candidate ∧
          candidate < P :=
      taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom hcandidate
    have hq_candidate : q < candidate := by
      dsimp [taoSection7Case3HeightExitBound] at hstrict_ltP
      omega
    have hpoint :
        pointAt candidate =
          (taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ (first :: before))
            (taoSection7SourceBlockStartS (first :: before))
            pre pres (candidate - q)).toPoint :=
      hsrc.pointAt_source_window candidate hq_candidate hstrict_ltP.2
    simpa [hpoint] using hsrc.white_iff_source candidate hcandidate
  · intro candidate hcandidate
    have hstrict_ltP :
        taoSection7Case3HeightExitBound
            (taoSection7Case3ExitGapBound A) q < candidate ∧
          candidate < P :=
      taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom hcandidate
    have hq_candidate : q < candidate := by
      dsimp [taoSection7Case3HeightExitBound] at hstrict_ltP
      omega
    have hpoint :
        pointAt candidate =
          (taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ (first :: before))
            (taoSection7SourceBlockStartS (first :: before))
            pre pres (candidate - q)).toPoint :=
      hsrc.pointAt_source_window candidate hq_candidate hstrict_ltP.2
    simpa [hpoint] using hsrc.domain_source candidate hcandidate

theorem TaoSection7Case3DistinguishedFullWindowSourceSuffixProvenance.to_distinguishedSourceSuffixProvenance
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {first : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hsrc :
      TaoSection7Case3DistinguishedFullWindowSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q
        blocks first before pre pres)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q) :
    TaoSection7Case3DistinguishedSourceSuffixProvenance
      W pointAt n J A xi epsilon P threshold q
      blocks first before pre pres := by
  refine
    { blocks_eq := hsrc.blocks_eq
      q_eq := hsrc.q_eq
      window_le := hsrc.window_le
      noThree_first := hsrc.noThree_first
      noThree_before := hsrc.noThree_before
      noThree_pre := hsrc.noThree_pre
      noThree_pres := hsrc.noThree_pres
      pointAt_source := ?_
      white_iff_source := hsrc.white_iff_source
      domain_source := hsrc.domain_source }
  intro t ht
  rcases Finset.mem_insert.mp ht with htq | ht_later
  · subst t
    simpa using hsrc.point_q
  · have hstrict_ltP :
        taoSection7Case3HeightExitBound
            (taoSection7Case3ExitGapBound A) q < t ∧
          t < P :=
      taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
        hroom ht_later
    have hq_t : q < t := by
      dsimp [taoSection7Case3HeightExitBound] at hstrict_ltP
      omega
    exact hsrc.pointAt_source_window t hq_t hstrict_ltP.2

theorem taoSection7Case3_exists_firstHitSourceProvenance_of_distinguishedFullWindowSourceSuffixProvenance
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {first : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hsrc :
      TaoSection7Case3DistinguishedFullWindowSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q
        blocks first before pre pres)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt A threshold P q pres.length old Γ candidate ∧
        ∃ hit Γ',
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt
              (taoSection7SourceBlockStartJ (first :: before))
              (taoSection7SourceBlockStartS (first :: before))
              pre pres P q old Γ' candidate hit := by
  exact
    taoSection7Case3_exists_firstHitSourceProvenance_of_fullWindowSourcePathData
      (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
      (xi := xi) (epsilon := epsilon) (family := family) (old := old)
      (P := P) (threshold := threshold) (q := q)
      (j := taoSection7SourceBlockStartJ (first :: before))
      (s := taoSection7SourceBlockStartS (first :: before))
      (pre := pre) (pres := pres)
      (hsrc.to_fullWindowSourcePathData hroom)
      hlow hroom hactive hcover

/--
The canonical `pointAt` function obtained by reading all offsets from one
global source-hit path.
-/
def taoSection7SourcePointAtOfBlocks
    (first : List ℕ) (rest : List (List ℕ)) : ℕ → TaoSection7Point :=
  fun t => (taoSection7SourceHitPathPoint (1 : ℕ+) 0 first rest t).toPoint

/--
Distinguished-first global path model for full-window source provenance.

This packages the strongest natural producer shape: `pointAt` agrees with the
global source-hit path from the initial block `first` throughout the inspected
`P` window.  The suffix full-window provenance then follows from the checked
prefix algebra `taoSection7SourceHitPathPoint_after_prefix_add`.
-/
structure TaoSection7Case3DistinguishedGlobalPathFullWindowProvenance
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
  point_q :
    pointAt q =
      (taoSection7SourceHitPoint
        (taoSection7SourceBlockStartJ (first :: before))
        (taoSection7SourceBlockStartS (first :: before)) pre).toPoint
  pointAt_global :
    ∀ t : ℕ,
      t < P →
        pointAt t =
          (taoSection7SourceHitPathPoint
            (1 : ℕ+) 0 first (before ++ pre :: pres) t).toPoint
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

theorem TaoSection7Case3DistinguishedGlobalPathFullWindowProvenance.of_sourcePointAtOfBlocks
    (W : ℕ → Prop)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {first : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hblocks : blocks = first :: before ++ pre :: pres)
    (hq : q = before.length + 1)
    (hP : P ≤ blocks.length)
    (hnoThree_first : taoSection7NoThree first)
    (hnoThree_before : ∀ block ∈ before, taoSection7NoThree block)
    (hnoThree_pre : taoSection7NoThree pre)
    (hnoThree_pres : ∀ block ∈ pres, taoSection7NoThree block)
    (hwhite :
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
              pre pres (candidate - q)).toPoint))
    (hdomain :
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
            pre pres (candidate - q)).toPoint) :
    TaoSection7Case3DistinguishedGlobalPathFullWindowProvenance
      W (taoSection7SourcePointAtOfBlocks first (before ++ pre :: pres))
      n J A xi epsilon P threshold q blocks first before pre pres := by
  refine
    { blocks_eq := hblocks
      q_eq := hq
      window_le := hP
      noThree_first := hnoThree_first
      noThree_before := hnoThree_before
      noThree_pre := hnoThree_pre
      noThree_pres := hnoThree_pres
      point_q := ?_
      pointAt_global := ?_
      white_iff_source := hwhite
      domain_source := hdomain }
  · subst q
    have hstartJ :
        taoSection7SourceBlockStartJFrom (1 : ℕ+) (first :: before) =
          taoSection7SourceBlockStartJ (first :: before) := by
      apply Subtype.ext
      simp [taoSection7SourceBlockStartJFrom,
        taoSection7SourceBlockStartJ, taoSection7ShiftIndex]
    have hstartS :
        taoSection7SourceBlockStartSFrom 0 (first :: before) =
          taoSection7SourceBlockStartS (first :: before) := by
      simp [taoSection7SourceBlockStartSFrom, taoSection7SourceBlockStartS]
    have hprefix :=
      taoSection7SourceHitPathPoint_after_prefix
        (j := (1 : ℕ+)) (s := 0) (first := first)
        (before := before) (pre := pre) (pres := pres)
    simpa [taoSection7SourcePointAtOfBlocks, hstartJ, hstartS] using
      congrArg TaoSection7RenewalPoint.toPoint hprefix
  · intro t _htP
    rfl

theorem TaoSection7Case3DistinguishedGlobalPathFullWindowProvenance.to_distinguishedFullWindowSourceSuffixProvenance
    {W : ℕ → Prop} {pointAt : ℕ → TaoSection7Point}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {first : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hglobal :
      TaoSection7Case3DistinguishedGlobalPathFullWindowProvenance
        W pointAt n J A xi epsilon P threshold q
        blocks first before pre pres) :
    TaoSection7Case3DistinguishedFullWindowSourceSuffixProvenance
      W pointAt n J A xi epsilon P threshold q
      blocks first before pre pres := by
  refine
    { blocks_eq := hglobal.blocks_eq
      q_eq := hglobal.q_eq
      window_le := hglobal.window_le
      noThree_first := hglobal.noThree_first
      noThree_before := hglobal.noThree_before
      noThree_pre := hglobal.noThree_pre
      noThree_pres := hglobal.noThree_pres
      point_q := hglobal.point_q
      pointAt_source_window := ?_
      white_iff_source := hglobal.white_iff_source
      domain_source := hglobal.domain_source }
  · intro t hq_t htP
    have hpoint := hglobal.pointAt_global t htP
    have ht_eq : t = before.length + (t - q) + 1 := by
      rw [hglobal.q_eq]
      rw [hglobal.q_eq] at hq_t
      omega
    have hidx_eq : before.length + (t - q) + 1 - q = t - q := by
      rw [hglobal.q_eq] at hq_t ⊢
      omega
    have hstartJ :
        taoSection7SourceBlockStartJFrom (1 : ℕ+) (first :: before) =
          taoSection7SourceBlockStartJ (first :: before) := by
      apply Subtype.ext
      simp [taoSection7SourceBlockStartJFrom,
        taoSection7SourceBlockStartJ, taoSection7ShiftIndex]
    have hstartS :
        taoSection7SourceBlockStartSFrom 0 (first :: before) =
          taoSection7SourceBlockStartS (first :: before) := by
      simp [taoSection7SourceBlockStartSFrom, taoSection7SourceBlockStartS]
    have hprefix :
        taoSection7SourceHitPathPoint (1 : ℕ+) 0 first
            (before ++ pre :: pres) (before.length + (t - q) + 1) =
          taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ (first :: before))
            (taoSection7SourceBlockStartS (first :: before))
            pre pres (t - q) := by
      have h :=
        taoSection7SourceHitPathPoint_after_prefix_add
          (j := (1 : ℕ+)) (s := 0) (first := first)
          (before := before) (pre := pre) (pres := pres) (n := t - q)
      simpa [hstartJ, hstartS] using h
    calc
      pointAt t =
          (taoSection7SourceHitPathPoint
            (1 : ℕ+) 0 first (before ++ pre :: pres) t).toPoint := hpoint
      _ =
          (taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ (first :: before))
            (taoSection7SourceBlockStartS (first :: before))
            pre pres (t - q)).toPoint := by
              rw [ht_eq]
              simpa [hidx_eq] using
                congrArg TaoSection7RenewalPoint.toPoint hprefix

theorem taoSection7Case3_exists_firstHitSourceProvenance_of_distinguishedGlobalPathFullWindowProvenance
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {first : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hglobal :
      TaoSection7Case3DistinguishedGlobalPathFullWindowProvenance
        W pointAt n J A xi epsilon P threshold q
        blocks first before pre pres)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt A threshold P q pres.length old Γ candidate ∧
        ∃ hit Γ',
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt
              (taoSection7SourceBlockStartJ (first :: before))
              (taoSection7SourceBlockStartS (first :: before))
              pre pres P q old Γ' candidate hit := by
  exact
    taoSection7Case3_exists_firstHitSourceProvenance_of_distinguishedFullWindowSourceSuffixProvenance
      (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
      (xi := xi) (epsilon := epsilon) (family := family) (old := old)
      (P := P) (threshold := threshold) (q := q)
      (blocks := blocks) (first := first) (before := before)
      (pre := pre) (pres := pres)
      (hglobal.to_distinguishedFullWindowSourceSuffixProvenance)
      hlow hroom hactive hcover

/--
Direct source-defined full-window producer for the distinguished block split.

This is the composed worker target: when `pointAt` is the canonical global
source-hit path from `first :: before ++ pre :: pres`, the checked prefix
algebra supplies full-window source provenance and hence the q-relative
first-hit source-provenance consumer.
-/
theorem taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePointAtOfBlocks
    (W : ℕ → Prop) [DecidablePred W]
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {first : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hblocks : blocks = first :: before ++ pre :: pres)
    (hq : q = before.length + 1)
    (hP : P ≤ blocks.length)
    (hnoThree_first : taoSection7NoThree first)
    (hnoThree_before : ∀ block ∈ before, taoSection7NoThree block)
    (hnoThree_pre : taoSection7NoThree pre)
    (hnoThree_pres : ∀ block ∈ pres, taoSection7NoThree block)
    (hwhite :
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
              pre pres (candidate - q)).toPoint))
    (hdomain :
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
            pre pres (candidate - q)).toPoint)
    (hlow :
      taoSection7Case3WindowWhiteCount
        W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family
        (taoSection7SourcePointAtOfBlocks first (before ++ pre :: pres))
        A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate Γ,
      TaoSection7Case3ActiveBlackPivotStepInLaterWindow
        W (taoSection7SourceBlackInDomain n xi epsilon J)
        family
        (taoSection7SourcePointAtOfBlocks first (before ++ pre :: pres))
        A threshold P q pres.length old Γ candidate ∧
        ∃ hit Γ',
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family
            (taoSection7SourcePointAtOfBlocks first (before ++ pre :: pres))
              (taoSection7SourceBlockStartJ (first :: before))
              (taoSection7SourceBlockStartS (first :: before))
              pre pres P q old Γ' candidate hit := by
  have hglobal :
      TaoSection7Case3DistinguishedGlobalPathFullWindowProvenance
        W (taoSection7SourcePointAtOfBlocks first (before ++ pre :: pres))
        n J A xi epsilon P threshold q blocks first before pre pres :=
    TaoSection7Case3DistinguishedGlobalPathFullWindowProvenance.of_sourcePointAtOfBlocks
      (W := W) (n := n) (J := J) (A := A) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (q := q) (blocks := blocks) (first := first)
      (before := before) (pre := pre) (pres := pres)
      hblocks hq hP hnoThree_first hnoThree_before hnoThree_pre
      hnoThree_pres hwhite hdomain
  exact
    taoSection7Case3_exists_firstHitSourceProvenance_of_distinguishedGlobalPathFullWindowProvenance
      (W := W)
      (pointAt :=
        taoSection7SourcePointAtOfBlocks first (before ++ pre :: pres))
      (n := n) (J := J) (A := A) (xi := xi) (epsilon := epsilon)
      (family := family) (old := old) (P := P) (threshold := threshold)
      (q := q) (blocks := blocks) (first := first) (before := before)
      (pre := pre) (pres := pres)
      hglobal hlow hroom hactive hcover

/--
One recursive encounter step with both accepted-transition and source-rebase
provenance at the q-relative first hit.

This is still a supplied-step package: it records the data future source and
stopping-process producers must supply, but does not prove that such a step
exists from Tao's recursive process.
-/
structure TaoSection7Case3EncounterStep
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    (P q : ℕ) (old Γ : TaoSection7Triangle) (first : ℕ) : Prop where
  accepted :
    TaoSection7Case3FirstHitAcceptedTransition
      black family pointAt Accepts q old Γ first
  first_ltP : first < P
  source_support :
    ∃ candidate : ℕ, ∃ j : ℕ+, ∃ s : ℕ, ∃ pre : List ℕ,
      ∃ pres : List (List ℕ),
        TaoSection7Case3FirstHitSourceProvenance
          black family pointAt j s pre pres P q old Γ candidate first

/--
Finite chain of source-supported q-relative encounter steps.

This is the closest support-only surface to Tao's `t_1,...,t_R` bookkeeping:
each step is an accepted first hit below the `P` window with source-rebase
provenance. The chain still does not prove that Tao's actual process reaches
this many steps.
-/
inductive TaoSection7Case3RecursiveEncounterChain
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    (P : ℕ) :
    ℕ → TaoSection7Triangle → List (ℕ × TaoSection7Triangle) → Prop
  | nil (q : ℕ) (old : TaoSection7Triangle) :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P q old []
  | cons {q first : ℕ} {old Γ : TaoSection7Triangle}
      {rest : List (ℕ × TaoSection7Triangle)}
      (hstep :
        TaoSection7Case3EncounterStep
          black family pointAt Accepts P q old Γ first)
      (htail :
        TaoSection7Case3RecursiveEncounterChain
          black family pointAt Accepts P first Γ rest) :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P q old ((first, Γ) :: rest)

namespace TaoSection7Case3RecursiveEncounterChain

theorem head_step
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P q old ((first, Γ) :: rest)) :
    TaoSection7Case3EncounterStep
      black family pointAt Accepts P q old Γ first := by
  cases hchain with
  | cons hstep _htail => exact hstep

theorem tail_chain
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P q old ((first, Γ) :: rest)) :
    TaoSection7Case3RecursiveEncounterChain
      black family pointAt Accepts P first Γ rest := by
  cases hchain with
  | cons _hstep htail => exact htail

theorem head_first_ltP
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P q old ((first, Γ) :: rest)) :
    first < P :=
  (head_step hchain).first_ltP

theorem head_q_lt_first
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P q old ((first, Γ) :: rest)) :
    q < first :=
  (head_step hchain).accepted.first_hit.1

theorem head_source_support
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P q old ((first, Γ) :: rest)) :
    ∃ candidate : ℕ, ∃ j : ℕ+, ∃ s : ℕ, ∃ pre : List ℕ,
      ∃ pres : List (List ℕ),
        TaoSection7Case3FirstHitSourceProvenance
          black family pointAt j s pre pres P q old Γ candidate first :=
  (head_step hchain).source_support

end TaoSection7Case3RecursiveEncounterChain

/--
Finite chain of q-relative accepted first-hit transitions.

This is a bookkeeping surface for Tao's later `t_i`/`r` bridge. The list
records only accepted first hits already supplied by the local first-stopping
API; it does not prove that the chain is maximal, that it is Tao's actual
recursive source process, or that it reaches length `R`.
-/
inductive TaoSection7Case3RecursiveFirstHitChain
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop) :
    ℕ → TaoSection7Triangle → List (ℕ × TaoSection7Triangle) → Prop
  | nil (q : ℕ) (old : TaoSection7Triangle) :
      TaoSection7Case3RecursiveFirstHitChain
        black family pointAt Accepts q old []
  | cons {q first : ℕ} {old Γ : TaoSection7Triangle}
      {rest : List (ℕ × TaoSection7Triangle)}
      (hstep :
        TaoSection7Case3FirstHitAcceptedTransition
          black family pointAt Accepts q old Γ first)
      (htail :
        TaoSection7Case3RecursiveFirstHitChain
          black family pointAt Accepts first Γ rest) :
      TaoSection7Case3RecursiveFirstHitChain
        black family pointAt Accepts q old ((first, Γ) :: rest)

namespace TaoSection7Case3RecursiveFirstHitChain

/-- Number of accepted first-hit transitions in the finite chain. -/
def length (steps : List (ℕ × TaoSection7Triangle)) : ℕ :=
  steps.length

/--
The optional `R`th transition time, using one-based `R` to match Tao's
notation `t_R`.
-/
def tR? : List (ℕ × TaoSection7Triangle) → ℕ → Option ℕ
  | [], _ => none
  | _step :: _rest, 0 => none
  | step :: _rest, 1 => some step.1
  | _step :: rest, R + 2 => tR? rest (R + 1)

/-- The finite chain has at least `R` accepted transitions. -/
def HasAtLeast (steps : List (ℕ × TaoSection7Triangle)) (R : ℕ) : Prop :=
  R ≤ steps.length

theorem head_accepted
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveFirstHitChain
        black family pointAt Accepts q old ((first, Γ) :: rest)) :
    TaoSection7Case3FirstHitAcceptedTransition
      black family pointAt Accepts q old Γ first := by
  cases hchain with
  | cons hstep _htail => exact hstep

theorem tail_chain
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveFirstHitChain
        black family pointAt Accepts q old ((first, Γ) :: rest)) :
    TaoSection7Case3RecursiveFirstHitChain
      black family pointAt Accepts first Γ rest := by
  cases hchain with
  | cons _hstep htail => exact htail

theorem head_q_lt_first
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveFirstHitChain
        black family pointAt Accepts q old ((first, Γ) :: rest)) :
    q < first := by
  exact (head_accepted hchain).first_hit.1

theorem head_new_ne_old
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveFirstHitChain
        black family pointAt Accepts q old ((first, Γ) :: rest)) :
    Γ ≠ old := by
  exact (head_accepted hchain).new_ne_old

end TaoSection7Case3RecursiveFirstHitChain

/--
A triangle hit in the restarted source process, before selecting which
triangle will be the current stopping triangle.
-/
def TaoSection7Case3TriangleHit
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle) (t : ℕ) : Prop :=
  ∃ Γ : TaoSection7Triangle, Γ ∈ family ∧ Γ.Mem (pointAt t)

/--
First triangle hit after a start index.

For Tao's `t_1` in the restarted process the intended start is `0`.
The later `t_i` use the stricter post-exit predicate
`TaoSection7Case3FirstAfterTriangleHitFrom` instead.
-/
def TaoSection7Case3FirstTriangleHitFrom
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (start t : ℕ) : Prop :=
  start < t ∧
    TaoSection7Case3TriangleHit pointAt family t ∧
      ∀ s : ℕ, start < s → s < t →
        ¬ TaoSection7Case3TriangleHit pointAt family s

/-- The initial `t_1` stopping step in Tao's restarted process. -/
structure TaoSection7Case3InitialStoppingStep
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (first : ℕ) (Γ : TaoSection7Triangle) : Prop where
  first_hit :
    TaoSection7Case3FirstTriangleHitFrom pointAt family 0 first
  mem_family : Γ ∈ family
  mem : Γ.Mem (pointAt first)

/--
One later stopping transition, from a previous stopping triangle to the first
later triangle hit after strict vertical exit from that previous triangle.
-/
structure TaoSection7Case3StoppingTransition
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (q : ℕ) (old : TaoSection7Triangle)
    (first : ℕ) (Γ : TaoSection7Triangle) : Prop where
  first_after_exit :
    TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first
  new_mem_family : Γ ∈ family
  new_mem : Γ.Mem (pointAt first)
  new_ne_old : Γ ≠ old

theorem taoSection7Case3_firstTriangleHitFrom_time_eq
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {start first first' : ℕ}
    (hfirst :
      TaoSection7Case3FirstTriangleHitFrom pointAt family start first)
    (hfirst' :
      TaoSection7Case3FirstTriangleHitFrom pointAt family start first') :
    first = first' := by
  by_contra hne
  by_cases hlt : first < first'
  · exact hfirst'.2.2 first hfirst.1 hlt hfirst.2.1
  · have hgt : first' < first := by omega
    exact hfirst.2.2 first' hfirst'.1 hgt hfirst'.2.1

theorem taoSection7Case3_firstAfterTriangleHitFrom_time_eq
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {q first first' : ℕ}
    (hfirst :
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first)
    (hfirst' :
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first') :
    first = first' := by
  by_contra hne
  by_cases hlt : first < first'
  · exact hfirst'.2.2 first hfirst.1 hlt hfirst.2.1
  · have hgt : first' < first := by omega
    exact hfirst.2.2 first' hfirst'.1 hgt hfirst'.2.1

theorem taoSection7Triangle_eq_of_familyPairwiseDisjoint_mem
    {family : Set TaoSection7Triangle}
    {Δ Γ : TaoSection7Triangle} {p : TaoSection7Point}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hΔ : Δ ∈ family) (hΓ : Γ ∈ family)
    (hΔ_mem : Δ.Mem p) (hΓ_mem : Γ.Mem p) :
    Δ = Γ := by
  by_contra hne
  exact
    TaoSection7TriangleFamilyPairwiseDisjoint.no_common_mem
      hpair hΔ hΓ hne hΔ_mem hΓ_mem

namespace TaoSection7Case3StoppingTransition

theorem pair_eq_of_pairwiseDisjoint
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q : ℕ} {old Γ Γ' : TaoSection7Triangle}
    {first first' : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hstep :
      TaoSection7Case3StoppingTransition
        pointAt family q old first Γ)
    (hstep' :
      TaoSection7Case3StoppingTransition
        pointAt family q old first' Γ') :
    (first, Γ) = (first', Γ') := by
  have hfirst_eq : first = first' :=
    taoSection7Case3_firstAfterTriangleHitFrom_time_eq
      hstep.first_after_exit hstep'.first_after_exit
  subst hfirst_eq
  have hΓ_eq : Γ = Γ' :=
    taoSection7Triangle_eq_of_familyPairwiseDisjoint_mem
      hpair hstep.new_mem_family hstep'.new_mem_family
      hstep.new_mem hstep'.new_mem
  subst hΓ_eq
  rfl

end TaoSection7Case3StoppingTransition

namespace TaoSection7Case3InitialStoppingStep

theorem pair_eq_of_pairwiseDisjoint
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {Γ Γ' : TaoSection7Triangle}
    {first first' : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hstep :
      TaoSection7Case3InitialStoppingStep pointAt family first Γ)
    (hstep' :
      TaoSection7Case3InitialStoppingStep pointAt family first' Γ') :
    (first, Γ) = (first', Γ') := by
  have hfirst_eq : first = first' :=
    taoSection7Case3_firstTriangleHitFrom_time_eq
      hstep.first_hit hstep'.first_hit
  subst hfirst_eq
  have hΓ_eq : Γ = Γ' :=
    taoSection7Triangle_eq_of_familyPairwiseDisjoint_mem
      hpair hstep.mem_family hstep'.mem_family hstep.mem hstep'.mem
  subst hΓ_eq
  rfl

end TaoSection7Case3InitialStoppingStep

namespace TaoSection7Case3FirstHitSourceProvenance

theorem to_stoppingTransition
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {P q : ℕ} {old Γ : TaoSection7Triangle}
    {candidate first : ℕ}
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first) :
    TaoSection7Case3StoppingTransition pointAt family q old first Γ :=
  ⟨hsrc.first_hit, hsrc.new_mem_family, hsrc.new_mem, hsrc.new_ne_old⟩

def to_rawOutsideEprimeEndpointData
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {P q : ℕ} {old Γ : TaoSection7Triangle}
    {candidate first : ℕ} {K B : ℝ}
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hbridge : TaoSection7Lemma710.LowTipBridge old Γ K B)
    (hl_close : |(pointAt first).lReal - (old.cornerL : ℝ)| ≤ K * B) :
    TaoSection7Lemma710.RawOutsideEprimeEndpointData
      old Γ (pointAt first) K B :=
  { endpoint_mem := hsrc.new_mem
    lower_bridge := hbridge
    l_close := hl_close }

/--
First-hit source-side controls for Lemma 7.10's lower-tip row witness.

This is the producer-side socket for the explicit row-budget data in
`Section7Geometry`: the first-hit provenance supplies the new-triangle endpoint
membership, while future outside-`E'` and large-`m` source estimates must fill
the endpoint bounds and old-row budgets here.
-/
structure OutsideEprimeBadLowerTipRowControls
    (pointAt : ℕ → TaoSection7Point)
    (old : TaoSection7Triangle)
    (q first : ℕ) (S Lerr Jerr gap : ℝ) : Prop where
  base_mem_old : old.Mem (pointAt q)
  s_def : S = ((old.cornerL - (pointAt q).l : ℤ) : ℝ)
  endpoint_l_lower : (old.cornerL : ℝ) ≤ (pointAt first).lReal
  endpoint_l_upper : (pointAt first).lReal - (old.cornerL : ℝ) ≤ Lerr
  endpoint_j_close :
    |(pointAt first).jReal - ((pointAt q).jReal + S / 4)| ≤ Jerr
  gap_nonneg : 0 ≤ gap
  Lerr_nonneg : 0 ≤ Lerr
  Jerr_nonneg : 0 ≤ Jerr
  old_left_budget :
    Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤ S / 4
  old_right_budget :
    (Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1)) * Real.log 9
      ≤ S * (Real.log 2 - Real.log 9 / 4)

/--
Build the row-control socket from cheap active/first-hit provenance plus
explicit analytic endpoint and scalar-margin estimates.

This still leaves the true outside-`E'` estimates `(7.63)/(7.64)` and the
large-`m` source-scale margin as hypotheses.
-/
theorem outsideEprimeBadLowerTipRowControls_of_active_firstHit_estimates
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A P q : ℕ} {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old Γ : TaoSection7Triangle} {candidate first : ℕ} {Lerr Jerr gap : ℝ}
    (hactive : TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hL : (pointAt first).lReal - (old.cornerL : ℝ) ≤ Lerr)
    (hJ :
      |(pointAt first).jReal -
        ((pointAt q).jReal + (((old.cornerL - (pointAt q).l : ℤ) : ℝ)) / 4)| ≤ Jerr)
    (hgap : 0 ≤ gap)
    (hLerr : 0 ≤ Lerr)
    (hJerr : 0 ≤ Jerr)
    (hE :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        (((old.cornerL - (pointAt q).l : ℤ) : ℝ)) *
          (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))) :
    OutsideEprimeBadLowerTipRowControls pointAt old q first
      (((old.cornerL - (pointAt q).l : ℤ) : ℝ)) Lerr Jerr gap := by
  have hS_nonneg : 0 ≤ (((old.cornerL - (pointAt q).l : ℤ) : ℝ)) := by
    have hheight : (pointAt q).l ≤ old.cornerL :=
      TaoSection7Triangle.mem_height_le hactive.pivot_mem
    have hint : 0 ≤ old.cornerL - (pointAt q).l := sub_nonneg.mpr hheight
    exact_mod_cast hint
  have hbudgets :=
    TaoSection7Lemma710.lemma710_oldRowBudgets_of_error_margin hS_nonneg hE
  refine
    { base_mem_old := hactive.pivot_mem
      s_def := rfl
      endpoint_l_lower := ?_
      endpoint_l_upper := hL
      endpoint_j_close := ?_
      gap_nonneg := hgap
      Lerr_nonneg := hLerr
      Jerr_nonneg := hJerr
      old_left_budget := hbudgets.1
      old_right_budget := hbudgets.2 }
  · have hheight_lt : old.cornerL < (pointAt first).l := hsrc.first_hit.2.1.1
    have hheight_le : old.cornerL ≤ (pointAt first).l := le_of_lt hheight_lt
    change ((old.cornerL : ℤ) : ℝ) ≤ (((pointAt first).l : ℤ) : ℝ)
    exact_mod_cast hheight_le
  · simpa using hJ

/--
Current-scale variant of the row-control constructor.

The future outside-`E'` producer may supply the horizontal error at `S^(3/5)`;
this theorem consumes the checked current-scale ledger and explicit absorption
premises to fill the old-row scalar margin.
-/
theorem outsideEprimeBadLowerTipRowControls_of_active_firstHit_currentScale_estimates
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {n A P q : ℕ} {j : ℕ+} {s : ℕ}
    {pre : List ℕ} {pres : List (List ℕ)}
    {old Γ : TaoSection7Triangle} {candidate first : ℕ}
    {M S Lerr Jerr gap CJS CJm : ℝ}
    (hactive : TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hscale :
      TaoSection7Lemma710CurrentScaleControls n old (pointAt q) M S)
    (hL_endpoint : (pointAt first).lReal - (old.cornerL : ℝ) ≤ Lerr)
    (hJ_endpoint :
      |(pointAt first).jReal - ((pointAt q).jReal + S / 4)| ≤ Jerr)
    (hgap : 0 ≤ gap)
    (hLerr : 0 ≤ Lerr)
    (hJerr : 0 ≤ Jerr)
    (hCJS_nonneg : 0 ≤ CJS)
    (hJ_scale : Jerr ≤ CJS * S ^ (3 / 5 : ℝ))
    (hJabsorb :
      CJS * ((Real.log 9 / Real.log 2) * M) ^ (3 / 5 : ℝ) ≤
        CJm * M ^ (3 / 5 : ℝ))
    (hmargin :
      CJm * M ^ (3 / 5 : ℝ) +
          ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ))) :
    OutsideEprimeBadLowerTipRowControls pointAt old q first S Lerr Jerr gap := by
  have hJ_m :
      Jerr ≤ CJm * M ^ (3 / 5 : ℝ) :=
    hscale.jerr_le_mpow_of_s_rpow_bound_absorb
      hCJS_nonneg hJ_scale hJabsorb
  have hE :
      Jerr + ((Real.log 2 / Real.log 9) * Lerr + 1) ≤
        S * (Real.log 2 / Real.log 9 - (1 / 4 : ℝ)) :=
    by linarith
  have hbudgets :=
    TaoSection7Lemma710.lemma710_oldRowBudgets_of_error_margin
      hscale.S_nonneg hE
  refine
    { base_mem_old := hactive.pivot_mem
      s_def := ?_
      endpoint_l_lower := ?_
      endpoint_l_upper := hL_endpoint
      endpoint_j_close := hJ_endpoint
      gap_nonneg := hgap
      Lerr_nonneg := hLerr
      Jerr_nonneg := hJerr
      old_left_budget := hbudgets.1
      old_right_budget := hbudgets.2 }
  · simpa [TaoSection7Triangle.verticalDepth] using hscale.S_def
  · have hheight_lt : old.cornerL < (pointAt first).l := hsrc.first_hit.2.1.1
    have hheight_le : old.cornerL ≤ (pointAt first).l := le_of_lt hheight_lt
    change ((old.cornerL : ℤ) : ℝ) ≤ (((pointAt first).l : ℤ) : ℝ)
    exact_mod_cast hheight_le

theorem to_outsideEprimeBadLowerTipRowData
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {P q : ℕ} {old Γ : TaoSection7Triangle}
    {candidate first : ℕ} {S Lerr Jerr gap : ℝ}
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hcontrols :
      OutsideEprimeBadLowerTipRowControls pointAt old q first S Lerr Jerr gap) :
    TaoSection7Lemma710.OutsideEprimeBadLowerTipRowData
      old Γ (pointAt q) (pointAt first) S Lerr Jerr gap :=
  { base_mem_old := hcontrols.base_mem_old
    endpoint_mem_new := hsrc.new_mem
    s_def := hcontrols.s_def
    endpoint_l_lower := hcontrols.endpoint_l_lower
    endpoint_l_upper := hcontrols.endpoint_l_upper
    endpoint_j_close := hcontrols.endpoint_j_close
    gap_nonneg := hcontrols.gap_nonneg
    Lerr_nonneg := hcontrols.Lerr_nonneg
    Jerr_nonneg := hcontrols.Jerr_nonneg
    old_left_budget := hcontrols.old_left_budget
    old_right_budget := hcontrols.old_right_budget }

/--
Convert checked lower-tip row controls into the raw common-point endpoint data
consumed by the deterministic `NearSigma` bridge.

This is still not endpoint production: the row controls and the `K*B`
absorptions are explicit inputs.
-/
theorem to_rawOutsideEprimeCommonPointEndpointData_from_rowControls
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {P q : ℕ} {old Γ : TaoSection7Triangle}
    {candidate first : ℕ} {S Lerr Jerr gap K B : ℝ}
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hcontrols :
      OutsideEprimeBadLowerTipRowControls pointAt old q first S Lerr Jerr gap)
    (hgap : gap ≤ K * B)
    (hLerr : Lerr ≤ K * B) :
    TaoSection7Lemma710.RawOutsideEprimeCommonPointEndpointData
      old Γ (pointAt first) gap K B := by
  have hrow :
      TaoSection7Lemma710.OutsideEprimeBadLowerTipRowData
        old Γ (pointAt q) (pointAt first) S Lerr Jerr gap :=
    hsrc.to_outsideEprimeBadLowerTipRowData hcontrols
  have hrowBridge :
      TaoSection7Lemma710.LowTipRowCommonPointBridge old Γ gap :=
    TaoSection7Lemma710.lowTipRowCommonPointBridge_of_outsideEprimeBadLowerTipRowData
      hrow
  have hcommon :
      TaoSection7Lemma710.LowTipCommonPointBridge old Γ gap :=
    TaoSection7Lemma710.lowTipCommonPointBridge_of_rowCommonPointBridge hrowBridge
  have hKB_nonneg : 0 ≤ K * B := le_trans hcontrols.Lerr_nonneg hLerr
  have hlower :
      -(K * B) ≤ (pointAt first).lReal - (old.cornerL : ℝ) := by
    have hdiff_nonneg :
        0 ≤ (pointAt first).lReal - (old.cornerL : ℝ) := by
      linarith [hcontrols.endpoint_l_lower]
    linarith
  have hupper :
      (pointAt first).lReal - (old.cornerL : ℝ) ≤ K * B :=
    le_trans hcontrols.endpoint_l_upper hLerr
  exact
    { endpoint_mem := hsrc.new_mem
      lower_common_bridge := hcommon
      gap_le := hgap
      l_close := abs_le.mpr ⟨hlower, hupper⟩ }

/--
Stopping-side deterministic localization for Lemma 7.10: once raw
common-point endpoint data is available, first-hit provenance supplies the
family facts needed by the geometry bridge to `NearSigma`.

This is not probability or endpoint production; the raw endpoint data and
radius bounds remain explicit inputs.
-/
theorem to_center_nearSigma_of_rawOutsideEprimeCommonPointEndpointData
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A P q : ℕ} {j : ℕ+} {s : ℕ}
    {pre : List ℕ} {pres : List (List ℕ)}
    {old Γ : TaoSection7Triangle}
    {candidate first : ℕ} {sMin gap K B J R : ℝ}
    (hactive : TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hsize : sMin ≤ Γ.size)
    (hJ : (Real.log 2 / Real.log 9) * (K * B + K * B) ≤ J)
    (hradius : J ^ 2 + (K * B) ^ 2 ≤ R ^ 2)
    (hdata :
      TaoSection7Lemma710.RawOutsideEprimeCommonPointEndpointData
        old Γ (pointAt first) gap K B) :
    ∃ c : TaoSection7Lemma710.Center family old sMin K B,
      c.triangle = Γ ∧
        TaoSection7Lemma710.NearSigma R
          (TaoSection7Lemma710.Sigma family old sMin K B) (pointAt first) :=
  TaoSection7Lemma710.rawOutsideEprimeCommonPointEndpointData_to_center_nearSigma
    hpair hactive.old_mem_family hsrc.new_mem_family hsrc.new_ne_old
    hsize hJ hradius hdata

/--
Stopping-side pointwise source-hit package for the outside-`E'` center event.
All analytic endpoint estimates remain explicit row-control and absorption
hypotheses.
-/
theorem to_outsideEprimeSourceHitData_from_rowControls
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A P q : ℕ} {j : ℕ+} {s : ℕ}
    {pre : List ℕ} {pres : List (List ℕ)}
    {old Γ : TaoSection7Triangle}
    {candidate first : ℕ} {sMin S Lerr Jerr gap K B J R : ℝ}
    (hactive : TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hsize : sMin ≤ Γ.size)
    (hJ : (Real.log 2 / Real.log 9) * (K * B + K * B) ≤ J)
    (hradius : J ^ 2 + (K * B) ^ 2 ≤ R ^ 2)
    (hcontrols :
      OutsideEprimeBadLowerTipRowControls pointAt old q first S Lerr Jerr gap)
    (hgap : gap ≤ K * B)
    (hLerr : Lerr ≤ K * B) :
    TaoSection7Lemma710.Lemma710OutsideEprimeSourceHitData
      family old Γ (pointAt first) sMin gap K B J R where
  pairwiseDisjoint := hpair
  old_mem_family := hactive.old_mem_family
  new_mem_family := hsrc.new_mem_family
  new_ne_old := hsrc.new_ne_old
  size_ge := hsize
  j_close_budget := hJ
  radius_absorbs := hradius
  raw_endpoint :=
    hsrc.to_rawOutsideEprimeCommonPointEndpointData_from_rowControls
      hcontrols hgap hLerr

theorem to_center_distSq_of_outsideEprimeSourceHitData
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {old Γ : TaoSection7Triangle}
    {first : ℕ} {sMin gap K B J R : ℝ}
    (hdata :
      TaoSection7Lemma710.Lemma710OutsideEprimeSourceHitData
        family old Γ (pointAt first) sMin gap K B J R) :
    ∃ c : TaoSection7Lemma710.Center family old sMin K B,
      c.triangle = Γ ∧ (pointAt first).distSq c.point ≤ R ^ 2 :=
  TaoSection7Lemma710.lemma710_outsideEprimeSourceHitData_to_center_distSq
    hdata

theorem to_firstHitAcceptedTransition
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {P q : ℕ} {old Γ : TaoSection7Triangle}
    {candidate first : ℕ}
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (haccept : Accepts q old first Γ) :
    TaoSection7Case3FirstHitAcceptedTransition
      black family pointAt Accepts q old Γ first :=
  ⟨hsrc.first_hit, hsrc.first_black, hsrc.new_mem_family,
    hsrc.new_mem, hsrc.new_ne_old, haccept⟩

theorem to_encounterStep
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {P q : ℕ} {old Γ : TaoSection7Triangle}
    {candidate first : ℕ}
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (haccept : Accepts q old first Γ) :
    TaoSection7Case3EncounterStep
      black family pointAt Accepts P q old Γ first :=
  { accepted := hsrc.to_firstHitAcceptedTransition haccept
    first_ltP := hsrc.first_ltP
    source_support := ⟨candidate, j, s, pre, pres, hsrc⟩ }

end TaoSection7Case3FirstHitSourceProvenance

theorem taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first candidate : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ}
    {pres : List (List ℕ)} {old Γ : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (haccept : Accepts q old first Γ) :
    ∃ before : List (List ℕ), ∃ next : List ℕ, ∃ after : List (List ℕ),
      pres = before ++ next :: after ∧
      before.length + 1 = first - q ∧
      TaoSection7Case3EncounterStep
        black family pointAt Accepts P q old Γ first ∧
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold first
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before))
        next after := by
  rcases
      taoSection7Case3_exists_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance_allWindowPackage
        (hfull := hfull) (hsrc := hsrc) hroom_first hfacts with
    ⟨before, next, after, hsplit, hidx, hrebase⟩
  exact
    ⟨before, next, after, hsplit, hidx, hsrc.to_encounterStep haccept,
      hrebase⟩

theorem taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first candidate : ℕ} {gapBound : ℕ → ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ}
    {pres : List (List ℕ)} {old Γ : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt j s pre pres P q old Γ candidate first)
    (hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (haccept : Accepts q old first Γ) :
    ∃ before : List (List ℕ), ∃ next : List ℕ, ∃ after : List (List ℕ),
      pres = before ++ next :: after ∧
      before.length + 1 = first - q ∧
      TaoSection7Case3EncounterStep
        black family pointAt Accepts P q old Γ first ∧
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold first gapBound
        (taoSection7SourceBlockStartJFrom j (pre :: before))
        (taoSection7SourceBlockStartSFrom s (pre :: before))
        next after := by
  rcases
      taoSection7Case3_exists_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance_allWindowFacts
        (hfull := hfull) (hsrc := hsrc) hroom_first
        hfacts.white_all hfacts.domain_all with
    ⟨before, next, after, hsplit, hidx, hrebase⟩
  exact
    ⟨before, next, after, hsplit, hidx, hsrc.to_encounterStep haccept,
      hrebase⟩

theorem taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathData_of_fullWindowSourcePathData
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound
            (taoSection7Case3ExitGapBound A) threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ old →
        Accepts q old first Γ) :
    ∃ candidate : ℕ, ∃ first : ℕ, ∃ Γ : TaoSection7Triangle,
      ∃ before : List (List ℕ), ∃ next : List ℕ,
        ∃ after : List (List ℕ),
          pres = before ++ next :: after ∧
          before.length + 1 = first - q ∧
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt j s pre pres P q old Γ candidate first ∧
          TaoSection7Case3EncounterStep
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt Accepts P q old Γ first ∧
          TaoSection7Case3FullWindowSourcePathData
            W pointAt n J A xi epsilon P threshold first
            (taoSection7SourceBlockStartJFrom j (pre :: before))
            (taoSection7SourceBlockStartSFrom s (pre :: before))
            next after := by
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_fullWindowSourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hfull hlow hroom hactive hcover with
    ⟨candidate, _pivot, _hpivot, first, Γ, hsrc⟩
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P first :=
    hroom_next first hsrc.first_hit.1 hsrc.first_ltP
  have haccept_step : Accepts q old first Γ :=
    haccept first Γ hsrc.first_ltP hsrc.first_black hsrc.first_hit
      hsrc.new_mem_family hsrc.new_mem hsrc.new_ne_old
  rcases
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance
        (hfull := hfull) (hsrc := hsrc)
        (hroom_first := hroom_first) (hfacts := hfacts)
        (haccept := haccept_step) with
    ⟨before, next, after, hsplit, hidx, hstep, hrebase⟩
  exact
    ⟨candidate, first, Γ, before, next, after, hsplit, hidx, hsrc, hstep,
      hrebase⟩

theorem taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_fullWindowSourcePathDataWithGap
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ old →
        Accepts q old first Γ) :
    ∃ candidate : ℕ, ∃ first : ℕ, ∃ Γ : TaoSection7Triangle,
      ∃ before : List (List ℕ), ∃ next : List ℕ,
        ∃ after : List (List ℕ),
          pres = before ++ next :: after ∧
          before.length + 1 = first - q ∧
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt j s pre pres P q old Γ candidate first ∧
          TaoSection7Case3EncounterStep
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt Accepts P q old Γ first ∧
          TaoSection7Case3FullWindowSourcePathDataWithGap
            W pointAt n J xi epsilon P threshold first gapBound
            (taoSection7SourceBlockStartJFrom j (pre :: before))
            (taoSection7SourceBlockStartSFrom s (pre :: before))
            next after := by
  have hdata :
      TaoSection7Case3SourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres :=
    hfull.to_sourcePathDataWithGap hroom
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_scale_coverage
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive hcover hfull.point_window with
    ⟨candidate, _pivot, _hpivot, first, Γ, hsrc⟩
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first :=
    hroom_next first hsrc.first_hit.1 hsrc.first_ltP
  have haccept_step : Accepts q old first Γ :=
    haccept first Γ hsrc.first_ltP hsrc.first_black hsrc.first_hit
      hsrc.new_mem_family hsrc.new_mem hsrc.new_ne_old
  rcases
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
        (hfull := hfull) (hsrc := hsrc)
        (hroom_first := hroom_first) (hfacts := hfacts)
        (haccept := haccept_step) with
    ⟨before, next, after, hsplit, hidx, hstep, hrebase⟩
  exact
    ⟨candidate, first, Γ, before, next, after, hsplit, hidx, hsrc, hstep,
      hrebase⟩

/--
State-preserving generic one-step support with the start-budget consequence.

The theorem carries the encounter step and rebased source state forward, and
derives `first <= B start` from the shared later-search right endpoint.  It
still does not choose or prove an abstract event-layer `Step start first`.
-/
theorem taoSection7Case3_exists_encounterStep_rebasedWithGap_and_budget_of_fullWindowSourcePathDataWithGap
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound B : ℕ → ℕ}
    {P start threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hq : q ∈ Finset.Icc start (start + threshold))
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hright :
      taoSection7Case3LaterSearchBound gapBound threshold
          (start + threshold) ≤ B start)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ old →
        Accepts q old first Γ) :
    ∃ candidate : ℕ, ∃ first : ℕ, ∃ Γ : TaoSection7Triangle,
      ∃ before : List (List ℕ), ∃ next : List ℕ,
        ∃ after : List (List ℕ),
          pres = before ++ next :: after ∧
          before.length + 1 = first - q ∧
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt j s pre pres P q old Γ candidate first ∧
          TaoSection7Case3EncounterStep
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt Accepts P q old Γ first ∧
          TaoSection7Case3FullWindowSourcePathDataWithGap
            W pointAt n J xi epsilon P threshold first gapBound
            (taoSection7SourceBlockStartJFrom j (pre :: before))
            (taoSection7SourceBlockStartSFrom s (pre :: before))
            next after ∧
          first ≤ B start := by
  have hdata :
      TaoSection7Case3SourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres :=
    hfull.to_sourcePathDataWithGap hroom
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_scale_coverage
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive hcover hfull.point_window with
    ⟨candidate, _pivot, hwindow, first, Γ, hsrc⟩
  have hfirst_budget : first ≤ B start :=
    taoSection7Case3_first_le_startBudget_of_laterWindow_rightBound
      hscale.gap_mono hq hwindow.mem_later_window
      hsrc.first_le_candidate hright
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first :=
    hroom_next first hsrc.first_hit.1 hsrc.first_ltP
  have haccept_step : Accepts q old first Γ :=
    haccept first Γ hsrc.first_ltP hsrc.first_black hsrc.first_hit
      hsrc.new_mem_family hsrc.new_mem hsrc.new_ne_old
  rcases
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
        (hfull := hfull) (hsrc := hsrc)
        (hroom_first := hroom_first) (hfacts := hfacts)
        (haccept := haccept_step) with
    ⟨before, next, after, hsplit, hidx, hstep, hrebase⟩
  exact
    ⟨candidate, first, Γ, before, next, after, hsplit, hidx, hsrc,
      hstep, hrebase, hfirst_budget⟩

/--
One-step producer-facing successor state for the generic `WithGap` recurrence.

This packages the checked first-hit/rebase step with the successor
active-triangle state obtained from the not-large-triangle event.  It still
assumes the acceptance and room facts needed by the local first-hit step; the
future source-derived indexed recurrence must supply those hypotheses at every
iteration.
-/
theorem taoSection7Case3_exists_nextActiveSourceStateWithGap_of_fullWindowSourcePathDataWithGap
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound B : ℕ → ℕ}
    {allowed : Set ℕ}
    {P start threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hq : q ∈ Finset.Icc start (start + threshold))
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hright :
      taoSection7Case3LaterSearchBound gapBound threshold
          (start + threshold) ≤ B start)
    (hallowed_first :
      ∀ first : ℕ, q < first → first < P → first ∈ allowed)
    (hnotLarge :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ old →
        Accepts q old first Γ) :
    ∃ first : ℕ, ∃ Γ : TaoSection7Triangle,
      ∃ jNext : ℕ+, ∃ sNext : ℕ, ∃ preNext : List ℕ,
        ∃ presNext : List (List ℕ),
          q < first ∧ first < P ∧ first ≤ B start ∧
          taoSection7Case3ExitRoom
            (taoSection7Case3LaterSearchBound gapBound threshold) P first ∧
          TaoSection7Case3EncounterStep
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt Accepts P q old Γ first ∧
          TaoSection7Case3ActiveTriangleAtWithBound
            family pointAt bound first Γ ∧
          TaoSection7Case3FullWindowSourcePathDataWithGap
            W pointAt n J xi epsilon P threshold first gapBound
            jNext sNext preNext presNext := by
  rcases
      taoSection7Case3_exists_encounterStep_rebasedWithGap_and_budget_of_fullWindowSourcePathDataWithGap
        (W := W) (pointAt := pointAt) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (B := B) (P := P) (start := start) (threshold := threshold)
        (q := q) (j := j) (s := s) (pre := pre) (pres := pres)
        (old := old) hq hfull hscale hlow hroom hactive hcover
        hroom_next hfacts hright haccept with
    ⟨_candidate, first, Γ, before, next, after, _hsplit, _hidx, hsrc,
      hstep, hrebase, hbudget⟩
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first :=
    hroom_next first hsrc.first_hit.1 hsrc.first_ltP
  have hallowed : first ∈ allowed :=
    hallowed_first first hsrc.first_hit.1 hsrc.first_ltP
  have hsmall : Γ.size < bound first :=
    taoSection7Case3_triangle_size_lt_of_not_large_union
      (pointAt := pointAt) (family := family) (allowed := allowed)
      (bound := bound) hnotLarge hallowed hsrc.new_mem_family hsrc.new_mem
  refine
    ⟨first, Γ, taoSection7SourceBlockStartJFrom j (pre :: before),
      taoSection7SourceBlockStartSFrom s (pre :: before), next, after,
      hsrc.first_hit.1, hsrc.first_ltP, hbudget, hroom_first, hstep, ?_,
      hrebase⟩
  exact
    { old_mem_family := hsrc.new_mem_family
      pivot_mem := hsrc.new_mem
      small_size := hsmall }

theorem taoSection7Case3_exists_stoppingTransition_and_rebasedFullWindowSourcePathData_of_fullWindowSourcePathData
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold q j s pre pres)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound
            (taoSection7Case3ExitGapBound A) threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P) :
    ∃ candidate : ℕ, ∃ first : ℕ, ∃ Γ : TaoSection7Triangle,
      ∃ before : List (List ℕ), ∃ next : List ℕ,
        ∃ after : List (List ℕ),
          pres = before ++ next :: after ∧
          before.length + 1 = first - q ∧
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family pointAt j s pre pres P q old Γ candidate first ∧
          TaoSection7Case3StoppingTransition pointAt family q old first Γ ∧
          TaoSection7Case3FullWindowSourcePathData
            W pointAt n J A xi epsilon P threshold first
            (taoSection7SourceBlockStartJFrom j (pre :: before))
            (taoSection7SourceBlockStartSFrom s (pre :: before))
            next after := by
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_fullWindowSourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hfull hlow hroom hactive hcover with
    ⟨candidate, _pivot, _hpivot, first, Γ, hsrc⟩
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P first :=
    hroom_next first hsrc.first_hit.1 hsrc.first_ltP
  rcases
      taoSection7Case3_exists_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance_allWindowPackage
        (hfull := hfull) (hsrc := hsrc) hroom_first hfacts with
    ⟨before, next, after, hsplit, hidx, hrebase⟩
  exact
    ⟨candidate, first, Γ, before, next, after, hsplit, hidx, hsrc,
      hsrc.to_stoppingTransition, hrebase⟩

namespace TaoSection7Case3FirstHitAcceptedTransition

theorem to_stoppingTransition
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    (hstep :
      TaoSection7Case3FirstHitAcceptedTransition
        black family pointAt Accepts q old Γ first) :
    TaoSection7Case3StoppingTransition pointAt family q old first Γ :=
  ⟨hstep.first_hit, hstep.new_mem_family, hstep.new_mem, hstep.new_ne_old⟩

end TaoSection7Case3FirstHitAcceptedTransition

theorem taoSection7Case3_exists_stoppingTransition_of_sourcePointAtOfBlocks
    (W : ℕ → Prop) [DecidablePred W]
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {firstBlock : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hblocks : blocks = firstBlock :: before ++ pre :: pres)
    (hq : q = before.length + 1)
    (hP : P ≤ blocks.length)
    (hnoThree_first : taoSection7NoThree firstBlock)
    (hnoThree_before : ∀ block ∈ before, taoSection7NoThree block)
    (hnoThree_pre : taoSection7NoThree pre)
    (hnoThree_pres : ∀ block ∈ pres, taoSection7NoThree block)
    (hwhite :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q + threshold) →
        (W candidate ↔
          taoSection7SourceWhitePoint n xi epsilon
            (taoSection7SourceHitPathPoint
              (taoSection7SourceBlockStartJ (firstBlock :: before))
              (taoSection7SourceBlockStartS (firstBlock :: before))
              pre pres (candidate - q)).toPoint))
    (hdomain :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q + threshold) →
        taoSection7SourcePointInDomain J
          (taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ (firstBlock :: before))
            (taoSection7SourceBlockStartS (firstBlock :: before))
            pre pres (candidate - q)).toPoint)
    (hlow :
      taoSection7Case3WindowWhiteCount
        W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family
        (taoSection7SourcePointAtOfBlocks firstBlock (before ++ pre :: pres))
        A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ candidate hit Γ,
      candidate < P ∧ hit ≤ candidate ∧ hit < P ∧
        TaoSection7Case3StoppingTransition
          (taoSection7SourcePointAtOfBlocks firstBlock (before ++ pre :: pres))
          family q old hit Γ ∧
        TaoSection7Case3FirstHitSourceProvenance
          (taoSection7SourceBlackInDomain n xi epsilon J)
          family
          (taoSection7SourcePointAtOfBlocks firstBlock (before ++ pre :: pres))
          (taoSection7SourceBlockStartJ (firstBlock :: before))
          (taoSection7SourceBlockStartS (firstBlock :: before))
          pre pres P q old Γ candidate hit := by
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePointAtOfBlocks
        (W := W) (n := n) (J := J) (A := A) (xi := xi)
        (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q)
        (blocks := blocks) (first := firstBlock) (before := before)
        (pre := pre) (pres := pres)
        hblocks hq hP hnoThree_first hnoThree_before hnoThree_pre
        hnoThree_pres hwhite hdomain hlow hroom hactive hcover with
    ⟨candidate, _candidateTriangle, hstep, hit, Γ, hsrc⟩
  exact
    ⟨candidate, hit, Γ, hstep.candidate_ltP, hsrc.first_le_candidate,
      hsrc.first_ltP, hsrc.to_stoppingTransition, hsrc⟩

theorem taoSection7Case3_exists_encounterStep_of_sourcePointAtOfBlocks
    (W : ℕ → Prop) [DecidablePred W]
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {firstBlock : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hblocks : blocks = firstBlock :: before ++ pre :: pres)
    (hq : q = before.length + 1)
    (hP : P ≤ blocks.length)
    (hnoThree_first : taoSection7NoThree firstBlock)
    (hnoThree_before : ∀ block ∈ before, taoSection7NoThree block)
    (hnoThree_pre : taoSection7NoThree pre)
    (hnoThree_pres : ∀ block ∈ pres, taoSection7NoThree block)
    (hwhite :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q + threshold) →
        (W candidate ↔
          taoSection7SourceWhitePoint n xi epsilon
            (taoSection7SourceHitPathPoint
              (taoSection7SourceBlockStartJ (firstBlock :: before))
              (taoSection7SourceBlockStartS (firstBlock :: before))
              pre pres (candidate - q)).toPoint))
    (hdomain :
      ∀ candidate : ℕ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q)
          (taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound A) q + threshold) →
        taoSection7SourcePointInDomain J
          (taoSection7SourceHitPathPoint
            (taoSection7SourceBlockStartJ (firstBlock :: before))
            (taoSection7SourceBlockStartS (firstBlock :: before))
            pre pres (candidate - q)).toPoint)
    (hlow :
      taoSection7Case3WindowWhiteCount
        W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family
        (taoSection7SourcePointAtOfBlocks firstBlock (before ++ pre :: pres))
        A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (haccept :
      ∀ hit Γ,
        hit < P →
          taoSection7SourceBlackInDomain n xi epsilon J
            ((taoSection7SourcePointAtOfBlocks
              firstBlock (before ++ pre :: pres)) hit) →
            TaoSection7Case3FirstAfterTriangleHitFrom
              (taoSection7SourcePointAtOfBlocks
                firstBlock (before ++ pre :: pres)) family old q hit →
              Γ ∈ family →
                Γ.Mem
                  ((taoSection7SourcePointAtOfBlocks
                    firstBlock (before ++ pre :: pres)) hit) →
                  Γ ≠ old →
                    Accepts q old hit Γ) :
    ∃ hit Γ,
      TaoSection7Case3EncounterStep
        (taoSection7SourceBlackInDomain n xi epsilon J)
        family
        (taoSection7SourcePointAtOfBlocks firstBlock (before ++ pre :: pres))
        Accepts P q old Γ hit := by
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePointAtOfBlocks
        (W := W) (n := n) (J := J) (A := A) (xi := xi)
        (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q)
        (blocks := blocks) (first := firstBlock) (before := before)
        (pre := pre) (pres := pres)
        hblocks hq hP hnoThree_first hnoThree_before hnoThree_pre
        hnoThree_pres hwhite hdomain hlow hroom hactive hcover with
    ⟨_candidate, _pivotΓ, _hpivot, hit, Γ, hsrc⟩
  refine ⟨hit, Γ, ?_⟩
  exact
    hsrc.to_encounterStep
      (haccept hit Γ hsrc.first_ltP hsrc.first_black hsrc.first_hit
        hsrc.new_mem_family hsrc.new_mem hsrc.new_ne_old)

theorem taoSection7Case3_exists_encounterStep_of_globalFullWindowSourceSuffixProvenance
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {blocks before : List (List ℕ)} {pre : List ℕ}
    {pres : List (List ℕ)}
    (hglobal :
      TaoSection7Case3GlobalFullWindowSourceSuffixProvenance
        W pointAt n J A xi epsilon P threshold q blocks before pre pres)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (haccept :
      ∀ first Γ,
        first < P →
          taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
            TaoSection7Case3FirstAfterTriangleHitFrom
              pointAt family old q first →
              Γ ∈ family →
                Γ.Mem (pointAt first) →
                  Γ ≠ old →
                    Accepts q old first Γ) :
    ∃ first Γ,
      TaoSection7Case3EncounterStep
        (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt Accepts P q old Γ first := by
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_globalFullWindowSourceSuffixProvenance
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q)
        (blocks := blocks) (before := before) (pre := pre) (pres := pres)
        hglobal hlow hroom hactive hcover with
    ⟨_candidate, _pivotΓ, _hpivot, first, Γ, hsrc⟩
  refine ⟨first, Γ, ?_⟩
  exact
    hsrc.to_encounterStep
      (haccept first Γ hsrc.first_ltP hsrc.first_black hsrc.first_hit
        hsrc.new_mem_family hsrc.new_mem hsrc.new_ne_old)

theorem taoSection7Case3_exists_encounterStep_of_distinguishedGlobalPathFullWindowProvenance
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {old : TaoSection7Triangle}
    {P threshold q : ℕ}
    {blocks : List (List ℕ)} {firstBlock : List ℕ}
    {before : List (List ℕ)} {pre : List ℕ} {pres : List (List ℕ)}
    (hsrc :
      TaoSection7Case3DistinguishedGlobalPathFullWindowProvenance
        W pointAt n J A xi epsilon P threshold q
        blocks firstBlock before pre pres)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (haccept :
      ∀ first Γ,
        first < P →
          taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
            TaoSection7Case3FirstAfterTriangleHitFrom
              pointAt family old q first →
              Γ ∈ family →
                Γ.Mem (pointAt first) →
                  Γ ≠ old →
                    Accepts q old first Γ) :
    ∃ hit Γ,
      TaoSection7Case3EncounterStep
        (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt Accepts P q old Γ hit := by
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_distinguishedGlobalPathFullWindowProvenance
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q)
        (blocks := blocks) (first := firstBlock) (before := before)
        (pre := pre) (pres := pres)
        hsrc hlow hroom hactive hcover with
    ⟨_candidate, _pivotΓ, _hpivot, hit, Γ, hfirst⟩
  refine ⟨hit, Γ, ?_⟩
  exact
    hfirst.to_encounterStep
      (haccept hit Γ hfirst.first_ltP hfirst.first_black hfirst.first_hit
        hfirst.new_mem_family hfirst.new_mem hfirst.new_ne_old)

namespace TaoSection7Case3StoppingTransition

theorem first_black_of_cover
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hstep :
      TaoSection7Case3StoppingTransition pointAt family q old first Γ) :
    black (pointAt first) :=
  taoSection7Case3_firstAfterTriangleHitFrom_black_of_cover
    hcover hstep.first_after_exit

theorem to_firstHitAcceptedTransition
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hstep :
      TaoSection7Case3StoppingTransition pointAt family q old first Γ)
    (haccept :
      black (pointAt first) →
        Accepts q old first Γ) :
    TaoSection7Case3FirstHitAcceptedTransition
      black family pointAt Accepts q old Γ first := by
  have hblack : black (pointAt first) :=
    first_black_of_cover hcover hstep
  exact
    ⟨hstep.first_after_exit, hblack, hstep.new_mem_family,
      hstep.new_mem, hstep.new_ne_old, haccept hblack⟩

end TaoSection7Case3StoppingTransition

/--
Tail of a Tao-style stopping trace after a current stopping triangle.

Each cons step advances from `(q, old)` to the next first post-exit triangle
hit `(first, Γ)`, then continues from that new state.
-/
inductive TaoSection7Case3StoppingTail
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    ℕ → TaoSection7Triangle → List (ℕ × TaoSection7Triangle) → Prop
  | nil (q : ℕ) (old : TaoSection7Triangle) :
      TaoSection7Case3StoppingTail pointAt family q old []
  | cons {q first : ℕ} {old Γ : TaoSection7Triangle}
      {rest : List (ℕ × TaoSection7Triangle)}
      (hstep :
        TaoSection7Case3StoppingTransition
          pointAt family q old first Γ)
      (htail :
        TaoSection7Case3StoppingTail pointAt family first Γ rest) :
      TaoSection7Case3StoppingTail
        pointAt family q old ((first, Γ) :: rest)

/--
Finite prefix of Tao's source stopping trace.

The empty prefix is allowed as a support object. A complete run below adds a
terminal condition saying whether no first hit exists or no later black point
exists after exiting the last triangle.
-/
inductive TaoSection7Case3StoppingPrefix
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    List (ℕ × TaoSection7Triangle) → Prop
  | nil : TaoSection7Case3StoppingPrefix pointAt family []
  | cons {first : ℕ} {Γ : TaoSection7Triangle}
      {rest : List (ℕ × TaoSection7Triangle)}
      (hinit :
        TaoSection7Case3InitialStoppingStep pointAt family first Γ)
      (htail :
        TaoSection7Case3StoppingTail pointAt family first Γ rest) :
      TaoSection7Case3StoppingPrefix pointAt family ((first, Γ) :: rest)

/-- No initial triangle hit exists after `start`. -/
def TaoSection7Case3NoInitialTriangleHitAfter
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle) (start : ℕ) : Prop :=
  ∀ t : ℕ, start < t → ¬ TaoSection7Case3TriangleHit pointAt family t

/--
Terminal condition after the last constructed stopping triangle: once the path
strictly exits that triangle vertically, no later point is black.
-/
def TaoSection7Case3NoLaterBlackAfterExit
    (black : TaoSection7Point → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (old : TaoSection7Triangle) : Prop :=
  ∀ t : ℕ, 0 < t → old.cornerL < (pointAt t).l → ¬ black (pointAt t)

/--
If every post-exit time has left the finite source domain horizontally, then
there are no later post-exit triangle hits for a family covering the
domain-gated source black set.
-/
theorem taoSection7Case3_noAfterTriangleHit_of_postExit_sourceDomainExit
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hout :
      ∀ t : ℕ, 0 < t →
        old.cornerL < (pointAt t).l →
          J < ((pointAt t).j : ℕ)) :
    ∀ t : ℕ, 0 < t →
      ¬ TaoSection7Case3AfterTriangleHit pointAt family old t := by
  intro t ht hhit
  rcases hhit with ⟨hexit, hmem⟩
  have hblack :
      taoSection7SourceBlackInDomain n xi epsilon J (pointAt t) :=
    (hcover (pointAt t)).mpr hmem
  exact (Nat.not_lt_of_ge (taoSection7SourceBlackInDomain_domain hblack))
    (hout t ht hexit)

namespace TaoSection7Case3NoLaterBlackAfterExit

/--
Terminality producer from the absence of any later post-exit triangle hit.

The family cover converts a hypothetical later black point into a later
triangle hit after `old`, contradicting `hnoAfter`.
-/
theorem of_noAfterTriangleHit
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hnoAfter :
      ∀ t : ℕ, 0 < t →
        ¬ TaoSection7Case3AfterTriangleHit pointAt family old t) :
    TaoSection7Case3NoLaterBlackAfterExit black pointAt old := by
  intro t ht hexit hblack
  exact hnoAfter t ht ⟨hexit, (hcover (pointAt t)).mp hblack⟩

/--
Terminality producer from a source-domain exit certificate after every
post-exit time.
-/
theorem of_postExit_sourceDomainExit
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hout :
      ∀ t : ℕ, 0 < t →
        old.cornerL < (pointAt t).l →
          J < ((pointAt t).j : ℕ)) :
    TaoSection7Case3NoLaterBlackAfterExit
      (taoSection7SourceBlackInDomain n xi epsilon J) pointAt old :=
  of_noAfterTriangleHit hcover
    (taoSection7Case3_noAfterTriangleHit_of_postExit_sourceDomainExit
      hcover hout)

end TaoSection7Case3NoLaterBlackAfterExit

/-- Last `(time, triangle)` pair of a finite stopping trace, if nonempty. -/
def TaoSection7Case3StoppingLast? :
    List (ℕ × TaoSection7Triangle) → Option (ℕ × TaoSection7Triangle)
  | [] => none
  | [step] => some step
  | _step :: rest => TaoSection7Case3StoppingLast? rest

/--
The terminal/maximality condition corresponding to Tao's definition of `r`.

For an empty trace, no initial triangle hit exists. For a nonempty trace, the
last stopping triangle admits no later black point after strict vertical exit.
-/
def TaoSection7Case3StoppingTerminal
    (black : TaoSection7Point → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    List (ℕ × TaoSection7Triangle) → Prop
  | [] => TaoSection7Case3NoInitialTriangleHitAfter pointAt family 0
  | steps =>
      match TaoSection7Case3StoppingLast? steps with
      | none => TaoSection7Case3NoInitialTriangleHitAfter pointAt family 0
      | some last =>
          TaoSection7Case3NoLaterBlackAfterExit black pointAt last.2

namespace TaoSection7Case3StoppingTerminal

theorem nil
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    (hterminal : TaoSection7Case3NoInitialTriangleHitAfter pointAt family 0) :
    TaoSection7Case3StoppingTerminal black pointAt family [] := by
  simpa [TaoSection7Case3StoppingTerminal] using hterminal

/--
Build the nonempty terminal/maximality condition from the explicit last
stopping triangle and the no-later-black-after-exit certificate.
-/
theorem of_last?_eq_some_noLaterBlackAfterExit
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    {last : ℕ × TaoSection7Triangle}
    (hlast : TaoSection7Case3StoppingLast? steps = some last)
    (hterminal :
      TaoSection7Case3NoLaterBlackAfterExit black pointAt last.2) :
    TaoSection7Case3StoppingTerminal black pointAt family steps := by
  cases steps with
  | nil =>
      simp [TaoSection7Case3StoppingLast?] at hlast
  | cons step rest =>
      dsimp [TaoSection7Case3StoppingTerminal]
      rw [hlast]
      exact hterminal

theorem singleton_of_noLaterBlackAfterExit
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {step : ℕ × TaoSection7Triangle}
    (hterminal :
      TaoSection7Case3NoLaterBlackAfterExit black pointAt step.2) :
    TaoSection7Case3StoppingTerminal black pointAt family [step] :=
  of_last?_eq_some_noLaterBlackAfterExit
    (by simp [TaoSection7Case3StoppingLast?]) hterminal

theorem noInitialTriangleHitAfter_of_nil
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    (hterminal :
      TaoSection7Case3StoppingTerminal black pointAt family []) :
    TaoSection7Case3NoInitialTriangleHitAfter pointAt family 0 := by
  simpa [TaoSection7Case3StoppingTerminal] using hterminal

theorem noLaterBlackAfterExit_of_last?_eq_some
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    {last : ℕ × TaoSection7Triangle}
    (hterminal :
      TaoSection7Case3StoppingTerminal black pointAt family steps)
    (hlast : TaoSection7Case3StoppingLast? steps = some last) :
    TaoSection7Case3NoLaterBlackAfterExit black pointAt last.2 := by
  cases steps with
  | nil =>
      simp [TaoSection7Case3StoppingLast?] at hlast
  | cons step rest =>
      dsimp [TaoSection7Case3StoppingTerminal] at hterminal
      rw [hlast] at hterminal
      exact hterminal

end TaoSection7Case3StoppingTerminal

/--
Complete finite source stopping run: a finite prefix together with the
maximality/terminal condition that defines the stopping count `r`.
-/
structure TaoSection7Case3SourceStoppingRun
    (black : TaoSection7Point → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (steps : List (ℕ × TaoSection7Triangle)) : Prop where
  trace_prefix : TaoSection7Case3StoppingPrefix pointAt family steps
  terminal_condition :
    TaoSection7Case3StoppingTerminal black pointAt family steps

namespace TaoSection7Case3RecursiveEncounterChain

theorem to_stoppingTail
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P q old steps) :
    TaoSection7Case3StoppingTail pointAt family q old steps := by
  induction hchain with
  | nil q old =>
      exact TaoSection7Case3StoppingTail.nil q old
  | cons hstep _htail ih =>
      exact TaoSection7Case3StoppingTail.cons
        hstep.accepted.to_stoppingTransition ih

theorem all_stop_ltP
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hchain :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P q old steps) :
    ∀ step ∈ steps, step.1 < P := by
  induction hchain with
  | nil q old =>
      intro step hmem
      simp at hmem
  | cons hstep _htail ih =>
      intro step hmem
      simp at hmem
      rcases hmem with hstep_eq | hmem_tail
      · cases hstep_eq
        exact hstep.first_ltP
      · exact ih step hmem_tail

end TaoSection7Case3RecursiveEncounterChain

namespace TaoSection7Case3StoppingTail

theorem head_step
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htail :
      TaoSection7Case3StoppingTail
        pointAt family q old ((first, Γ) :: rest)) :
    TaoSection7Case3StoppingTransition pointAt family q old first Γ := by
  cases htail with
  | cons hstep _htail => exact hstep

theorem tail
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htail :
      TaoSection7Case3StoppingTail
        pointAt family q old ((first, Γ) :: rest)) :
    TaoSection7Case3StoppingTail pointAt family first Γ rest := by
  cases htail with
  | cons _hstep htail => exact htail

theorem head_time_gt
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htail :
      TaoSection7Case3StoppingTail
        pointAt family q old ((first, Γ) :: rest)) :
    q < first :=
  (head_step htail).first_after_exit.1

theorem to_recursiveFirstHitChain
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (htail :
      TaoSection7Case3StoppingTail pointAt family q old steps)
    (haccept :
      ∀ {q first : ℕ} {old Γ : TaoSection7Triangle},
        TaoSection7Case3StoppingTransition pointAt family q old first Γ →
          black (pointAt first) →
            Accepts q old first Γ) :
    TaoSection7Case3RecursiveFirstHitChain
      black family pointAt Accepts q old steps := by
  induction htail with
  | nil q old =>
      exact TaoSection7Case3RecursiveFirstHitChain.nil q old
  | cons hstep htail ih =>
      have haccepted :
          TaoSection7Case3FirstHitAcceptedTransition
            black family pointAt Accepts _ _ _ _ :=
        TaoSection7Case3StoppingTransition.to_firstHitAcceptedTransition
          hcover hstep (haccept hstep)
      exact TaoSection7Case3RecursiveFirstHitChain.cons haccepted ih

theorem take
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (htail :
      TaoSection7Case3StoppingTail pointAt family q old steps)
    (R : ℕ) :
    TaoSection7Case3StoppingTail pointAt family q old (steps.take R) := by
  induction htail generalizing R with
  | nil q old =>
      simpa using
        TaoSection7Case3StoppingTail.nil
          (pointAt := pointAt) (family := family) q old
  | cons hstep _htail ih =>
      cases R with
      | zero =>
          simpa using
            TaoSection7Case3StoppingTail.nil
              (pointAt := pointAt) (family := family) _ _
      | succ Rtail =>
          simpa using TaoSection7Case3StoppingTail.cons hstep (ih Rtail)

end TaoSection7Case3StoppingTail

namespace TaoSection7Case3StoppingPrefix

theorem head_initial
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hprefix :
      TaoSection7Case3StoppingPrefix pointAt family ((first, Γ) :: rest)) :
    TaoSection7Case3InitialStoppingStep pointAt family first Γ := by
  cases hprefix with
  | cons hinit _htail => exact hinit

theorem tail
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hprefix :
      TaoSection7Case3StoppingPrefix pointAt family ((first, Γ) :: rest)) :
    TaoSection7Case3StoppingTail pointAt family first Γ rest := by
  cases hprefix with
  | cons _hinit htail => exact htail

theorem head_time_pos
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hprefix :
      TaoSection7Case3StoppingPrefix pointAt family ((first, Γ) :: rest)) :
    0 < first :=
  (head_initial hprefix).first_hit.1

theorem tail_recursiveFirstHitChain
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (hprefix :
      TaoSection7Case3StoppingPrefix pointAt family ((first, Γ) :: rest))
    (haccept :
      ∀ {q first : ℕ} {old Γ : TaoSection7Triangle},
        TaoSection7Case3StoppingTransition pointAt family q old first Γ →
          black (pointAt first) →
            Accepts q old first Γ) :
    TaoSection7Case3RecursiveFirstHitChain
      black family pointAt Accepts first Γ rest :=
  TaoSection7Case3StoppingTail.to_recursiveFirstHitChain
    hcover (tail hprefix) haccept

theorem take
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (R : ℕ) :
    TaoSection7Case3StoppingPrefix pointAt family (steps.take R) := by
  cases hprefix with
  | nil =>
      simpa using
        TaoSection7Case3StoppingPrefix.nil
          (pointAt := pointAt) (family := family)
  | cons hinit htail =>
      cases R with
      | zero =>
          simpa using
            TaoSection7Case3StoppingPrefix.nil
              (pointAt := pointAt) (family := family)
      | succ Rtail =>
          simpa using
            TaoSection7Case3StoppingPrefix.cons hinit
              (TaoSection7Case3StoppingTail.take htail Rtail)

end TaoSection7Case3StoppingPrefix

namespace TaoSection7Case3SourceStoppingRun

theorem of_prefix_terminal
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (hterminal : TaoSection7Case3StoppingTerminal black pointAt family steps) :
    TaoSection7Case3SourceStoppingRun black pointAt family steps :=
  ⟨hprefix, hterminal⟩

theorem nil_of_noInitialTriangleHitAfter
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    (hterminal : TaoSection7Case3NoInitialTriangleHitAfter pointAt family 0) :
    TaoSection7Case3SourceStoppingRun black pointAt family [] :=
  of_prefix_terminal TaoSection7Case3StoppingPrefix.nil
    (TaoSection7Case3StoppingTerminal.nil hterminal)

theorem of_prefix_last?_noLaterBlackAfterExit
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    {last : ℕ × TaoSection7Triangle}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (hlast : TaoSection7Case3StoppingLast? steps = some last)
    (hterminal :
      TaoSection7Case3NoLaterBlackAfterExit black pointAt last.2) :
    TaoSection7Case3SourceStoppingRun black pointAt family steps :=
  of_prefix_terminal hprefix
    (TaoSection7Case3StoppingTerminal.of_last?_eq_some_noLaterBlackAfterExit
      hlast hterminal)

theorem cons_of_initial_tail_terminal
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hinit : TaoSection7Case3InitialStoppingStep pointAt family first Γ)
    (htail : TaoSection7Case3StoppingTail pointAt family first Γ rest)
    (hterminal :
      TaoSection7Case3StoppingTerminal
        black pointAt family ((first, Γ) :: rest)) :
    TaoSection7Case3SourceStoppingRun
      black pointAt family ((first, Γ) :: rest) :=
  of_prefix_terminal (TaoSection7Case3StoppingPrefix.cons hinit htail)
    hterminal

theorem cons_of_initial_tail_last?_noLaterBlackAfterExit
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    {last : ℕ × TaoSection7Triangle}
    (hinit : TaoSection7Case3InitialStoppingStep pointAt family first Γ)
    (htail : TaoSection7Case3StoppingTail pointAt family first Γ rest)
    (hlast :
      TaoSection7Case3StoppingLast? ((first, Γ) :: rest) = some last)
    (hterminal :
      TaoSection7Case3NoLaterBlackAfterExit black pointAt last.2) :
    TaoSection7Case3SourceStoppingRun
      black pointAt family ((first, Γ) :: rest) :=
  of_prefix_last?_noLaterBlackAfterExit
    (TaoSection7Case3StoppingPrefix.cons hinit htail) hlast hterminal

/-- The finite stopping count represented by a complete run. -/
def r (steps : List (ℕ × TaoSection7Triangle)) : ℕ :=
  steps.length

/-- One-based accessor for Tao's `t_R`. -/
def tR? : List (ℕ × TaoSection7Triangle) → ℕ → Option ℕ
  | [], _ => none
  | _step :: _rest, 0 => none
  | step :: _rest, 1 => some step.1
  | _step :: rest, R + 2 => tR? rest (R + 1)

/-- The run has at least `R` constructed stopping times. -/
def HasAtLeast (steps : List (ℕ × TaoSection7Triangle)) (R : ℕ) : Prop :=
  R ≤ r steps

/--
Endpoint package needed by the Case 3 counting layer. Future source iteration
work must prove this from the complete stopping run and low-window hypotheses;
this definition itself is only bookkeeping.
-/
def HasTWithinWindow
    (steps : List (ℕ × TaoSection7Triangle)) (R P : ℕ) : Prop :=
  ∃ t : ℕ, tR? steps R = some t ∧ t < P

/--
Finite prefix package for the deterministic Case 3 endpoint route.

This deliberately does not require the terminal/maximality condition of a full
`TaoSection7Case3SourceStoppingRun`: it is the producer surface for proving an
`R`-long stopping prefix inside the finite `P` window before the final
no-later-black argument is available.
-/
structure PrefixWindowData
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (steps : List (ℕ × TaoSection7Triangle)) (R P : ℕ) : Prop where
  trace_prefix : TaoSection7Case3StoppingPrefix pointAt family steps
  hasAtLeast : HasAtLeast steps R
  all_stop_ltP : ∀ step ∈ steps, step.1 < P

theorem prefixWindowData_of_prefix_hasAtLeast_all_ltP
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R P : ℕ}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (hR : HasAtLeast steps R)
    (hall : ∀ step ∈ steps, step.1 < P) :
    PrefixWindowData pointAt family steps R P :=
  ⟨hprefix, hR, hall⟩

theorem tR?_some_length_le
    {steps : List (ℕ × TaoSection7Triangle)} {R tR : ℕ}
    (htR : tR? steps R = some tR) :
    R ≤ steps.length := by
  induction steps generalizing R tR with
  | nil =>
      cases R <;> simp [tR?] at htR
  | cons step rest ih =>
      cases R with
      | zero =>
          simp
      | succ Rpred =>
          cases Rpred with
          | zero =>
              simp
          | succ Rtail =>
              have hrest :
                  Rtail + 1 ≤ rest.length :=
                ih (R := Rtail + 1) (tR := tR) (by
                  simpa [tR?] using htR)
              simp
              omega

theorem tR?_isSome_pos
    {steps : List (ℕ × TaoSection7Triangle)} {R : ℕ}
    (h : (tR? steps R).isSome = true) :
    0 < R := by
  cases R with
  | zero =>
      cases steps <;> simp [tR?] at h
  | succ R =>
      exact Nat.succ_pos R

theorem tR?_take_eq_of_tR?
    {steps : List (ℕ × TaoSection7Triangle)} {R tR : ℕ}
    (htR : tR? steps R = some tR) :
    tR? (steps.take R) R = some tR := by
  induction steps generalizing R tR with
  | nil =>
      cases R <;> simp [tR?] at htR
  | cons step rest ih =>
      cases R with
      | zero =>
          simp [tR?] at htR
      | succ Rpred =>
          cases Rpred with
          | zero =>
              simpa [tR?] using htR
          | succ Rtail =>
              have hrest :
                  tR? (rest.take (Rtail + 1)) (Rtail + 1) =
                    some tR :=
                ih (R := Rtail + 1) (tR := tR) (by
                  simpa [tR?] using htR)
              simpa [tR?] using hrest

theorem tR?_take_self
    (steps : List (ℕ × TaoSection7Triangle)) (R : ℕ) :
    tR? (steps.take R) R = tR? steps R := by
  induction steps generalizing R with
  | nil =>
      cases R <;> simp [tR?]
  | cons step rest ih =>
      cases R with
      | zero =>
          simp [tR?]
      | succ Rpred =>
          cases Rpred with
          | zero =>
              simp [tR?]
          | succ Rtail =>
              simpa [tR?] using ih (Rtail + 1)

/--
If a finite stopping list has at least `R` entries and every recorded stopping
time lies below `P`, then the one-based `t_R` accessor lies inside the same
P-window.

This is only list bookkeeping. Future source iteration work must still prove
`0 < R`, `HasAtLeast steps R`, and the per-stop window bound.
-/
theorem hasTWithinWindow_of_hasAtLeast_all_ltP
    {steps : List (ℕ × TaoSection7Triangle)} {R P : ℕ}
    (hRpos : 0 < R)
    (hR : HasAtLeast steps R)
    (hall : ∀ step ∈ steps, step.1 < P) :
    HasTWithinWindow steps R P := by
  induction steps generalizing R with
  | nil =>
      simp [HasAtLeast, r] at hR
      omega
  | cons step rest ih =>
      cases R with
      | zero =>
          omega
      | succ Rpred =>
          cases Rpred with
          | zero =>
              refine ⟨step.1, ?_, ?_⟩
              · simp [tR?]
              · exact hall step (by simp)
          | succ Rtail =>
              have hRtail_pos : 0 < Rtail + 1 := by omega
              have hRtail :
                  HasAtLeast rest (Rtail + 1) := by
                simp [HasAtLeast, r] at hR ⊢
                omega
              have hall_tail : ∀ tailStep ∈ rest, tailStep.1 < P := by
                intro tailStep htailStep
                exact hall tailStep (by simp [htailStep])
              rcases ih hRtail_pos hRtail hall_tail with
                ⟨t, htR, htP⟩
              refine ⟨t, ?_, htP⟩
              simpa [tR?] using htR

theorem stoppingTail_base_lt_tR_of_tR?
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R tR : ℕ}
    (htail :
      TaoSection7Case3StoppingTail pointAt family q old steps)
    (htR : tR? steps R = some tR) :
    q < tR := by
  induction steps generalizing q old R tR with
  | nil =>
      cases htail
      cases R <;> simp [tR?] at htR
  | cons step rest ih =>
      cases step with
      | mk first Γ =>
          cases htail with
          | cons hstep htail =>
              cases R with
              | zero =>
                  simp [tR?] at htR
              | succ Rpred =>
                  cases Rpred with
                  | zero =>
                      simp [tR?] at htR
                      cases htR
                      exact hstep.first_after_exit.1
                  | succ Rtail =>
                      have hrest :
                          tR? rest (Rtail + 1) = some tR := by
                        simpa [tR?] using htR
                      exact
                        lt_trans hstep.first_after_exit.1
                          (ih (q := first) (old := Γ)
                            (R := Rtail + 1) (tR := tR)
                            htail hrest)

theorem stoppingTail_all_stop_le_tR_of_mem_take
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R tR : ℕ}
    (htail :
      TaoSection7Case3StoppingTail pointAt family q old steps)
    (htR : tR? steps R = some tR) :
    ∀ step ∈ steps.take R, step.1 ≤ tR := by
  induction steps generalizing q old R tR with
  | nil =>
      intro step hmem
      simp at hmem
  | cons head rest ih =>
      cases head with
      | mk first Γ =>
          cases htail with
          | cons hstep htail =>
              cases R with
              | zero =>
                  intro step hmem
                  simp at hmem
              | succ Rpred =>
                  cases Rpred with
                  | zero =>
                      intro step hmem
                      have hstep_eq : step = (first, Γ) := by
                        simpa using hmem
                      cases hstep_eq
                      simp [tR?] at htR
                      cases htR
                      exact le_rfl
                  | succ Rtail =>
                      have hrest :
                          tR? rest (Rtail + 1) = some tR := by
                        simpa [tR?] using htR
                      intro step hmem
                      simp at hmem
                      rcases hmem with hhead | htailmem
                      · cases hhead
                        exact
                          le_of_lt
                            (stoppingTail_base_lt_tR_of_tR?
                              htail hrest)
                      · exact
                          ih (q := first) (old := Γ)
                            (R := Rtail + 1) (tR := tR)
                            htail hrest step htailmem

theorem stoppingPrefix_all_stop_le_tR_of_mem_take
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R tR : ℕ}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (htR : tR? steps R = some tR) :
    ∀ step ∈ steps.take R, step.1 ≤ tR := by
  induction steps generalizing R tR with
  | nil =>
      intro step hmem
      simp at hmem
  | cons head rest _ih =>
      cases head with
      | mk first Γ =>
          cases hprefix with
          | cons _hinit htail =>
              cases R with
              | zero =>
                  intro step hmem
                  simp at hmem
              | succ Rpred =>
                  cases Rpred with
                  | zero =>
                      intro step hmem
                      have hstep_eq : step = (first, Γ) := by
                        simpa using hmem
                      cases hstep_eq
                      simp [tR?] at htR
                      cases htR
                      exact le_rfl
                  | succ Rtail =>
                      have hrest :
                          tR? rest (Rtail + 1) = some tR := by
                        simpa [tR?] using htR
                      intro step hmem
                      simp at hmem
                      rcases hmem with hhead | htailmem
                      · cases hhead
                        exact
                          le_of_lt
                            (stoppingTail_base_lt_tR_of_tR?
                              htail hrest)
                      · exact
                          stoppingTail_all_stop_le_tR_of_mem_take
                            htail hrest step htailmem

theorem prefixWindowData_of_tR_ltP_take
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R tR P : ℕ}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (htR : tR? steps R = some tR)
    (htR_ltP : tR < P) :
    PrefixWindowData pointAt family (steps.take R) R P := by
  have hlen : R ≤ steps.length := tR?_some_length_le htR
  refine
    { trace_prefix := TaoSection7Case3StoppingPrefix.take hprefix R
      hasAtLeast := ?_
      all_stop_ltP := ?_ }
  · simp [HasAtLeast, r, List.length_take, Nat.min_eq_left hlen]
  · intro step hmem
    exact
      lt_of_le_of_lt
        (stoppingPrefix_all_stop_le_tR_of_mem_take
          hprefix htR step hmem)
        htR_ltP

namespace PrefixWindowData

theorem hasTWithinWindow
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R P : ℕ}
    (hdata : PrefixWindowData pointAt family steps R P)
    (hRpos : 0 < R) :
    HasTWithinWindow steps R P :=
  hasTWithinWindow_of_hasAtLeast_all_ltP
    hRpos hdata.hasAtLeast hdata.all_stop_ltP

theorem not_low_window_of_many_positive
    (W : ℕ → Prop) [DecidablePred W]
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R P threshold : ℕ}
    (hdata : PrefixWindowData pointAt family steps R P)
    (hRpos : 0 < R)
    (hmany :
      ∀ t : ℕ,
        tR? steps R = some t →
          threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold := by
  rcases hdata.hasTWithinWindow hRpos with ⟨t, htR, htP⟩
  exact taoSection7Case3_many_positive_offsets_not_low_window
    W htP (hmany t htR)

end PrefixWindowData

/--
Endpoint bridge from a source stopping-run accessor to the existing finite
P-window counting contradiction.

Future Lemma 7.9 work should supply the positive-offset lower bound at the
actual `t_R`; future source iteration work should supply `HasTWithinWindow`.
This lemma only performs the endpoint/count-window transfer.
-/
theorem not_low_window_of_hasTWithinWindow_many_positive
    (W : ℕ → Prop) [DecidablePred W]
    {steps : List (ℕ × TaoSection7Triangle)} {R P threshold : ℕ}
    (hwithin : HasTWithinWindow steps R P)
    (hmany :
      ∀ t : ℕ,
        tR? steps R = some t →
          threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold := by
  rcases hwithin with ⟨t, htR, htP⟩
  exact taoSection7Case3_many_positive_offsets_not_low_window
    W htP (hmany t htR)

/--
Pointwise form of the same endpoint/count-window bridge when the caller has
already extracted the actual `t_R`.
-/
theorem not_low_window_of_tR_many_positive
    (W : ℕ → Prop) [DecidablePred W]
    {steps : List (ℕ × TaoSection7Triangle)} {R P threshold t : ℕ}
    (htR : tR? steps R = some t)
    (htP : t < P)
    (hmany : threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  not_low_window_of_hasTWithinWindow_many_positive
    (W := W) (steps := steps) (R := R) (P := P)
    (threshold := threshold) ⟨t, htR, htP⟩
    (fun t' ht' => by
      rw [htR] at ht'
      cases ht'
      exact hmany)

/--
Combined assumption-consuming adapter: if future source iteration work proves
the run has at least `R` stops and all recorded stop times are inside the
P-window, and future Lemma 7.9 work supplies the positive-offset lower bound at
the extracted `t_R`, then the low P-window event is impossible.
-/
theorem not_low_window_of_hasAtLeast_all_ltP_many_positive
    (W : ℕ → Prop) [DecidablePred W]
    {steps : List (ℕ × TaoSection7Triangle)} {R P threshold : ℕ}
    (hRpos : 0 < R)
    (hR : HasAtLeast steps R)
    (hall : ∀ step ∈ steps, step.1 < P)
    (hmany :
      ∀ t : ℕ,
        tR? steps R = some t →
          threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  not_low_window_of_hasTWithinWindow_many_positive
    (W := W) (steps := steps) (R := R) (P := P)
    (threshold := threshold)
    (hasTWithinWindow_of_hasAtLeast_all_ltP hRpos hR hall)
    hmany

theorem not_low_window_of_run_hasTWithinWindow_many_positive
    (W : ℕ → Prop) [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R P threshold : ℕ}
    (_hrun :
      TaoSection7Case3SourceStoppingRun black pointAt family steps)
    (hwithin : HasTWithinWindow steps R P)
    (hmany :
      ∀ t : ℕ,
        tR? steps R = some t →
          threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  not_low_window_of_hasTWithinWindow_many_positive
    (W := W) (steps := steps) (R := R) (P := P)
    (threshold := threshold) hwithin hmany

theorem not_low_window_of_run_hasAtLeast_all_ltP_many_positive
    (W : ℕ → Prop) [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R P threshold : ℕ}
    (hrun :
      TaoSection7Case3SourceStoppingRun black pointAt family steps)
    (hRpos : 0 < R)
    (hR : HasAtLeast steps R)
    (hall : ∀ step ∈ steps, step.1 < P)
    (hmany :
      ∀ t : ℕ,
        tR? steps R = some t →
          threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  not_low_window_of_run_hasTWithinWindow_many_positive
    (W := W) (steps := steps) (R := R) (P := P)
    (threshold := threshold) hrun
    (hasTWithinWindow_of_hasAtLeast_all_ltP hRpos hR hall)
    hmany

theorem head_initial_of_run
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        black pointAt family ((first, Γ) :: rest)) :
    TaoSection7Case3InitialStoppingStep pointAt family first Γ :=
  TaoSection7Case3StoppingPrefix.head_initial hrun.trace_prefix

theorem tail_of_run
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        black pointAt family ((first, Γ) :: rest)) :
    TaoSection7Case3StoppingTail pointAt family first Γ rest :=
  TaoSection7Case3StoppingPrefix.tail hrun.trace_prefix

theorem head_time_pos_of_run
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        black pointAt family ((first, Γ) :: rest)) :
    0 < first :=
  TaoSection7Case3StoppingPrefix.head_time_pos hrun.trace_prefix

theorem tail_recursiveFirstHitChain_of_run
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        black pointAt family ((first, Γ) :: rest))
    (hcover : TaoSection7TriangleFamilyCoverBlack black family)
    (haccept :
      ∀ {q first : ℕ} {old Γ : TaoSection7Triangle},
        TaoSection7Case3StoppingTransition pointAt family q old first Γ →
          black (pointAt first) →
            Accepts q old first Γ) :
    TaoSection7Case3RecursiveFirstHitChain
      black family pointAt Accepts first Γ rest :=
  TaoSection7Case3StoppingPrefix.tail_recursiveFirstHitChain
    hcover hrun.trace_prefix haccept

theorem trace_prefix_of_run
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hrun :
      TaoSection7Case3SourceStoppingRun black pointAt family steps) :
    TaoSection7Case3StoppingPrefix pointAt family steps :=
  hrun.trace_prefix

theorem terminal_condition_of_run
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hrun :
      TaoSection7Case3SourceStoppingRun black pointAt family steps) :
    TaoSection7Case3StoppingTerminal black pointAt family steps :=
  hrun.terminal_condition

end TaoSection7Case3SourceStoppingRun

/--
Producer-facing data for Tao's constructed source stopping run at a fixed
cutoff.

This is still only a socket: future source-iteration work must produce the
run, the `R <= r` evidence, the concrete `t_R`, and the Lemma 7.9 count
identity for the same `steps`.
-/
structure TaoSection7Case3ConstructedSourceStoppingRunData
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (n J : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (steps : List (ℕ × TaoSection7Triangle))
    (R tR lemma79Count : ℕ) : Prop where
  source_run :
    TaoSection7Case3SourceStoppingRun
      (taoSection7SourceBlackInDomain n xi epsilon J) pointAt family steps
  R_pos : 0 < R
  R_le_r : TaoSection7Case3SourceStoppingRun.HasAtLeast steps R
  tR_eq : TaoSection7Case3SourceStoppingRun.tR? steps R = some tR
  count_identity :
    lemma79Count = taoSection7Case3PositiveWhiteCount W tR

/--
Event-free source identity for Tao's restarted Case 3 stopping run.

This records that the finite stopping run and the low-window predicate are tied
to one restarted source trajectory.  It deliberately does not contain
outside-`E*` evidence, `F*`/Markov evidence, endpoint-window production, or
probability budgets.
-/
structure TaoSection7Case3ActualRunSourceIdentity
    (sourceAt : ℕ → TaoSection7Point) (restart : ℕ)
    (W : ℕ → Prop) [DecidablePred W]
    (black : TaoSection7Point → Prop)
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (n J : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P : ℕ)
    (steps : List (ℕ × TaoSection7Triangle))
    (R tR lemma79Count : ℕ) : Prop where
  restart_pointAt :
    ∀ p : ℕ, p < P → pointAt p = sourceAt (restart + p)
  sameW :
    TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P
  black_iff_source :
    ∀ p : ℕ, p < P →
      (black (pointAt p) ↔
        taoSection7SourceBlackPoint n xi epsilon (pointAt p))
  source_run :
    TaoSection7Case3SourceStoppingRun black pointAt family steps
  R_pos : 0 < R
  R_le_r : TaoSection7Case3SourceStoppingRun.HasAtLeast steps R
  tR_eq : TaoSection7Case3SourceStoppingRun.tR? steps R = some tR
  count_identity :
    lemma79Count = taoSection7Case3PositiveWhiteCount W tR

namespace TaoSection7Case3ActualRunSourceIdentity

theorem of_sourceBlackInDomain_sourceRun
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count : ℕ}
    (hrestart : ∀ p : ℕ, p < P → pointAt p = sourceAt (restart + p))
    (hfacts : TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hRpos : 0 < R)
    (hR : TaoSection7Case3SourceStoppingRun.HasAtLeast steps R)
    (htR : TaoSection7Case3SourceStoppingRun.tR? steps R = some tR)
    (hcount :
      lemma79Count = taoSection7Case3PositiveWhiteCount W tR) :
    TaoSection7Case3ActualRunSourceIdentity
      sourceAt restart W (taoSection7SourceBlackInDomain n xi epsilon J)
      pointAt family n J xi epsilon P steps R tR lemma79Count where
  restart_pointAt := hrestart
  sameW := hfacts
  black_iff_source := by
    intro p hp
    exact hfacts.blackInDomain_iff_sourceBlackPoint hp
  source_run := hrun
  R_pos := hRpos
  R_le_r := hR
  tR_eq := htR
  count_identity := hcount

theorem sourceWhite_iff
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count p : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (hp : p < P) :
    W p ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt p) :=
  h.sameW.white_all p hp

theorem sourceDomain
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count p : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (hp : p < P) :
    taoSection7SourcePointInDomain J (pointAt p) :=
  h.sameW.domain_all p hp

theorem sourceAt_of_restart
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count p : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (hp : p < P) :
    sourceAt (restart + p) = pointAt p :=
  (h.restart_pointAt p hp).symm

theorem tracePrefix
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count) :
    TaoSection7Case3StoppingPrefix pointAt family steps :=
  h.source_run.trace_prefix

/--
The terminal condition is relative to the restarted `pointAt` path carried by
the actual-run identity.  Converting from an unrestarted ambient source path is
a separate suffix-reindexing obligation.
-/
theorem terminalCondition
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count) :
    TaoSection7Case3StoppingTerminal black pointAt family steps :=
  h.source_run.terminal_condition

theorem R_le_r_steps
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count) :
    R ≤ TaoSection7Case3SourceStoppingRun.r steps := by
  simpa [TaoSection7Case3SourceStoppingRun.HasAtLeast] using h.R_le_r

theorem hasTWithinWindow_of_tR_ltP
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (htR_ltP : tR < P) :
    TaoSection7Case3SourceStoppingRun.HasTWithinWindow steps R P :=
  ⟨tR, h.tR_eq, htR_ltP⟩

theorem prefixWindowData_of_all_stop_ltP
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (hall : ∀ step ∈ steps, step.1 < P) :
    TaoSection7Case3SourceStoppingRun.PrefixWindowData
      pointAt family steps R P :=
  { trace_prefix := h.source_run.trace_prefix
    hasAtLeast := h.R_le_r
    all_stop_ltP := hall }

theorem prefixWindowData_of_tR_ltP_take
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (htR_ltP : tR < P) :
    TaoSection7Case3SourceStoppingRun.PrefixWindowData
      pointAt family (steps.take R) R P :=
  TaoSection7Case3SourceStoppingRun.prefixWindowData_of_tR_ltP_take
    h.source_run.trace_prefix h.tR_eq htR_ltP

/--
Endpoint-window extractor for actual-run identities.

If later source iteration work proves that every recorded stop of the actual
run lies below the finite window `P`, then the accessed `t_R` carried by the
identity also lies below `P`.  This removes the endpoint half of the
outside-low-white certificate from callers that can already produce the
per-stop window bound.
-/
theorem tR_ltP_of_all_stop_ltP
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (hall : ∀ step ∈ steps, step.1 < P) :
    tR < P := by
  rcases
      TaoSection7Case3SourceStoppingRun.hasTWithinWindow_of_hasAtLeast_all_ltP
        h.R_pos h.R_le_r hall with
    ⟨t, htR, htP⟩
  rw [h.tR_eq] at htR
  cases htR
  exact htP

/--
Count-window consumer for the actual-run identity.  The endpoint fact `tR < P`
is an explicit downstream input, so this lemma does not produce endpoint-window
credit.
-/
theorem not_low_window_of_tR_ltP_many_positive
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count threshold : ℕ}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (htR_ltP : tR < P)
    (hmany : threshold < lemma79Count) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold := by
  exact
    TaoSection7Case3SourceStoppingRun.not_low_window_of_tR_many_positive
      (W := W) (steps := steps) (R := R) (P := P)
      (threshold := threshold) (t := tR)
      h.tR_eq htR_ltP
      (by simpa [h.count_identity] using hmany)

end TaoSection7Case3ActualRunSourceIdentity

namespace TaoSection7Case3ConstructedSourceStoppingRunData

/--
Build constructed source-run data from explicit terminal/maximality evidence.

This removes the opaque `source_run` premise, but still leaves the real
producer obligations visible: the stopping prefix, the last-triangle
no-later-black certificate, the cutoff evidence, the `t_R` accessor equality,
and the Lemma 7.9 count identity.
-/
theorem of_prefix_last?_noLaterBlackAfterExit
    {W : ℕ → Prop} [DecidablePred W]
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {last : ℕ × TaoSection7Triangle}
    {R tR lemma79Count : ℕ}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (hlast : TaoSection7Case3StoppingLast? steps = some last)
    (hterminal :
      TaoSection7Case3NoLaterBlackAfterExit
        (taoSection7SourceBlackInDomain n xi epsilon J) pointAt last.2)
    (hRpos : 0 < R)
    (hR : TaoSection7Case3SourceStoppingRun.HasAtLeast steps R)
    (htR : TaoSection7Case3SourceStoppingRun.tR? steps R = some tR)
    (hcount :
      lemma79Count = taoSection7Case3PositiveWhiteCount W tR) :
    TaoSection7Case3ConstructedSourceStoppingRunData
      W pointAt family n J xi epsilon steps R tR lemma79Count where
  source_run :=
    TaoSection7Case3SourceStoppingRun.of_prefix_last?_noLaterBlackAfterExit
      hprefix hlast hterminal
  R_pos := hRpos
  R_le_r := hR
  tR_eq := htR
  count_identity := hcount

/--
Constructed source-run data closes the actual-run source identity specialized
to Tao's domain-gated source black predicate.

This remains a producer socket: the data itself still has to supply the source
run, the cutoff evidence, the `t_R` accessor equality, and the Lemma 7.9 count
identity for the same `steps`.
-/
theorem to_actualRunSourceIdentity
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {R tR lemma79Count : ℕ}
    (hdata :
      TaoSection7Case3ConstructedSourceStoppingRunData
        W pointAt family n J xi epsilon steps R tR lemma79Count)
    (hrestart : ∀ p : ℕ, p < P → pointAt p = sourceAt (restart + p))
    (hfacts : TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P) :
    TaoSection7Case3ActualRunSourceIdentity
      sourceAt restart W (taoSection7SourceBlackInDomain n xi epsilon J)
      pointAt family n J xi epsilon P steps R tR lemma79Count :=
  TaoSection7Case3ActualRunSourceIdentity.of_sourceBlackInDomain_sourceRun
    hrestart hfacts hdata.source_run hdata.R_pos hdata.R_le_r hdata.tR_eq
    hdata.count_identity

end TaoSection7Case3ConstructedSourceStoppingRunData

/--
Samplewise actual-run identities feed the deterministic inner `(7.56)` subset
socket.

The remaining outside-bad-event work is explicit in `houtside`: for every
sample outside both `E*_used` and `F*`, it must provide the endpoint-window
fact `t_R < P` and the Lemma 7.9/Markov many-white lower bound at that same
`t_R`.  This theorem only performs the low-window contradiction step and then
uses the generic `LowWhite ⊆ E*_used ∪ F*` wrapper.
-/
theorem taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity
    {Ω : Type*}
    {sourceAt : Ω → ℕ → TaoSection7Point}
    {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {black : Ω → TaoSection7Point → Prop}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P R threshold : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count : Ω → ℕ}
    {EStarUsed FSlack : Set Ω}
    (hidentity :
      ∀ ω : Ω,
        TaoSection7Case3ActualRunSourceIdentity
          (sourceAt ω) (restart ω) (W ω) (black ω) (pointAt ω) family
          n J xi epsilon P (steps ω) R (tR ω) (lemma79Count ω))
    (houtside :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        tR ω < P ∧ threshold < lemma79Count ω) :
    taoSection7Case3LowWhiteEvent W P threshold ⊆ EStarUsed ∪ FSlack := by
  refine taoSection7Case3_lowWhite_subset_EStarUsed_union_FSlack ?_
  intro ω hlow hnotE hnotF
  rcases houtside ω hnotE hnotF with ⟨htR_ltP, hmany⟩
  have hnotLow :
      ¬ taoSection7Case3WindowWhiteCount (W ω) P ≤ threshold :=
    (hidentity ω).not_low_window_of_tR_ltP_many_positive htR_ltP hmany
  exact hnotLow (by
    simpa [taoSection7Case3LowWhiteEvent, taoSection7Case3LowWhite] using
      hlow)

/--
Variant of the actual-run low-white subset bridge whose endpoint half is
derived from a per-sample all-stops-below-`P` certificate.

The many-white lower bound remains explicit.  The endpoint producer is now the
more source-facing statement that all stops in the actual run remain inside
the finite `P` window.
-/
theorem taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_all_stop_ltP
    {Ω : Type*}
    {sourceAt : Ω → ℕ → TaoSection7Point}
    {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {black : Ω → TaoSection7Point → Prop}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P R threshold : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count : Ω → ℕ}
    {EStarUsed FSlack : Set Ω}
    (hidentity :
      ∀ ω : Ω,
        TaoSection7Case3ActualRunSourceIdentity
          (sourceAt ω) (restart ω) (W ω) (black ω) (pointAt ω) family
          n J xi epsilon P (steps ω) R (tR ω) (lemma79Count ω))
    (hall_stop :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        ∀ step ∈ steps ω, step.1 < P)
    (hmany :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        threshold < lemma79Count ω) :
    taoSection7Case3LowWhiteEvent W P threshold ⊆ EStarUsed ∪ FSlack := by
  refine
    taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity
      (hidentity := hidentity) ?_
  intro ω hnotE hnotF
  exact
    ⟨(hidentity ω).tR_ltP_of_all_stop_ltP (hall_stop ω hnotE hnotF),
      hmany ω hnotE hnotF⟩

namespace TaoSection7Case3StoppingPrefix

/--
Prefix-named alias for the finite R-prefix window package.  The underlying
definition lives near the `t_R` accessors, but this namespace makes clear that
the data does not require terminal source-run maximality.
-/
abbrev WindowData
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (steps : List (ℕ × TaoSection7Triangle)) (R P : ℕ) : Prop :=
  TaoSection7Case3SourceStoppingRun.PrefixWindowData
    pointAt family steps R P

theorem windowData_of_prefix_hasAtLeast_all_ltP
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R P : ℕ}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (hR : TaoSection7Case3SourceStoppingRun.HasAtLeast steps R)
    (hall : ∀ step ∈ steps, step.1 < P) :
    WindowData pointAt family steps R P :=
  TaoSection7Case3SourceStoppingRun.prefixWindowData_of_prefix_hasAtLeast_all_ltP
    hprefix hR hall

theorem hasTWithinWindow_of_prefix_hasAtLeast_all_ltP
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R P : ℕ}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (hRpos : 0 < R)
    (hR : TaoSection7Case3SourceStoppingRun.HasAtLeast steps R)
    (hall : ∀ step ∈ steps, step.1 < P) :
    TaoSection7Case3SourceStoppingRun.HasTWithinWindow steps R P :=
  (windowData_of_prefix_hasAtLeast_all_ltP hprefix hR hall).hasTWithinWindow
    hRpos

theorem not_low_window_of_prefix_hasAtLeast_all_ltP_many_positive
    (W : ℕ → Prop) [DecidablePred W]
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R P threshold : ℕ}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (hRpos : 0 < R)
    (hR : TaoSection7Case3SourceStoppingRun.HasAtLeast steps R)
    (hall : ∀ step ∈ steps, step.1 < P)
    (hmany :
      ∀ t : ℕ,
        TaoSection7Case3SourceStoppingRun.tR? steps R = some t →
          threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  TaoSection7Case3SourceStoppingRun.PrefixWindowData.not_low_window_of_many_positive
    (W := W)
    (windowData_of_prefix_hasAtLeast_all_ltP hprefix hR hall) hRpos hmany

theorem all_stop_le_tR_of_mem_take
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R tR : ℕ}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (htR :
      TaoSection7Case3SourceStoppingRun.tR? steps R = some tR) :
    ∀ step ∈ steps.take R, step.1 ≤ tR :=
  TaoSection7Case3SourceStoppingRun.stoppingPrefix_all_stop_le_tR_of_mem_take
    hprefix htR

theorem windowData_of_tR_ltP_take
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)} {R tR P : ℕ}
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (htR :
      TaoSection7Case3SourceStoppingRun.tR? steps R = some tR)
    (htR_ltP : tR < P) :
    WindowData pointAt family (steps.take R) R P :=
  TaoSection7Case3SourceStoppingRun.prefixWindowData_of_tR_ltP_take
    hprefix htR htR_ltP

theorem windowData_of_initial_and_encounterChain
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P R first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hinit : TaoSection7Case3InitialStoppingStep pointAt family first Γ)
    (hfirst_ltP : first < P)
    (hchain :
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P first Γ rest)
    (hR :
      TaoSection7Case3SourceStoppingRun.HasAtLeast
        ((first, Γ) :: rest) R) :
    WindowData pointAt family ((first, Γ) :: rest) R P := by
  have htail :
      TaoSection7Case3StoppingTail pointAt family first Γ rest :=
    TaoSection7Case3RecursiveEncounterChain.to_stoppingTail hchain
  have hprefix :
      TaoSection7Case3StoppingPrefix
        pointAt family ((first, Γ) :: rest) :=
    TaoSection7Case3StoppingPrefix.cons hinit htail
  have htail_ltP : ∀ step ∈ rest, step.1 < P :=
    TaoSection7Case3RecursiveEncounterChain.all_stop_ltP hchain
  have hall :
      ∀ step ∈ ((first, Γ) :: rest), step.1 < P := by
    intro step hmem
    simp at hmem
    rcases hmem with hstep_eq | hmem_tail
    · cases hstep_eq
      exact hfirst_ltP
    · exact htail_ltP step hmem_tail
  exact windowData_of_prefix_hasAtLeast_all_ltP hprefix hR hall

end TaoSection7Case3StoppingPrefix

/--
Assumption socket for the finite R-prefix layer.

This deliberately bundles an already-produced initial stopping step, recursive
encounter chain, and length lower bound.  It is not the source-derived
R-prefix producer.
-/
structure TaoSection7Case3PrefixRInputs
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    (P R first : ℕ) (Γ : TaoSection7Triangle)
    (rest : List (ℕ × TaoSection7Triangle)) : Prop where
  initial : TaoSection7Case3InitialStoppingStep pointAt family first Γ
  first_ltP : first < P
  encounter_chain :
    TaoSection7Case3RecursiveEncounterChain
      black family pointAt Accepts P first Γ rest
  hasAtLeast :
    TaoSection7Case3SourceStoppingRun.HasAtLeast
      ((first, Γ) :: rest) R

namespace TaoSection7Case3PrefixRInputs

theorem windowData
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P R first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hdata :
      TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P R first Γ rest) :
    TaoSection7Case3StoppingPrefix.WindowData
      pointAt family ((first, Γ) :: rest) R P :=
  TaoSection7Case3StoppingPrefix.windowData_of_initial_and_encounterChain
    hdata.initial hdata.first_ltP hdata.encounter_chain hdata.hasAtLeast

theorem hasTWithinWindow
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P R first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hdata :
      TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P R first Γ rest)
    (hRpos : 0 < R) :
    TaoSection7Case3SourceStoppingRun.HasTWithinWindow
      ((first, Γ) :: rest) R P :=
  hdata.windowData.hasTWithinWindow hRpos

theorem all_stop_ltP
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P R first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hdata :
      TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P R first Γ rest) :
    ∀ step ∈ ((first, Γ) :: rest), step.1 < P :=
  hdata.windowData.all_stop_ltP

theorem not_low_window_of_many_positive
    (W : ℕ → Prop) [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P R threshold first : ℕ} {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hdata :
      TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P R first Γ rest)
    (hRpos : 0 < R)
    (hmany :
      ∀ t : ℕ,
        TaoSection7Case3SourceStoppingRun.tR?
            ((first, Γ) :: rest) R = some t →
          threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  hdata.windowData.not_low_window_of_many_positive W hRpos hmany

end TaoSection7Case3PrefixRInputs

/--
Outside-event form of the all-stops producer supplied by finite R-prefix
inputs.

This is the checked producer for the endpoint half of the current
outside-low-white certificate when the actual-run list has already been
identified with the constructed prefix list.
-/
theorem taoSection7Case3_hall_stop_of_prefixRInputs
    {Ω : Type*}
    {black : Ω → TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {Accepts : Ω → ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P R : ℕ}
    {first : Ω → ℕ}
    {Γ : Ω → TaoSection7Triangle}
    {rest steps : Ω → List (ℕ × TaoSection7Triangle)}
    {EStarUsed FSlack : Set Ω}
    (hprefix :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        TaoSection7Case3PrefixRInputs
          (black ω) family (pointAt ω) (Accepts ω) P R
          (first ω) (Γ ω) (rest ω))
    (hsteps :
      ∀ ω : Ω, steps ω = (first ω, Γ ω) :: rest ω) :
    ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
      ∀ step ∈ steps ω, step.1 < P := by
  intro ω hnotE hnotF step hmem
  have hmem_prefix : step ∈ (first ω, Γ ω) :: rest ω := by
    simpa [hsteps ω] using hmem
  exact (hprefix ω hnotE hnotF).all_stop_ltP step hmem_prefix

namespace TaoSection7Case3ActualRunSourceIdentity

/--
Endpoint-window extractor from the source-facing finite R-prefix package.

This removes the raw all-stops-below-`P` function when the caller has already
assembled `TaoSection7Case3PrefixRInputs` for the actual stopping prefix.
-/
theorem tR_ltP_of_prefixRInputs
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J P R first tR lemma79Count : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        ((first, Γ) :: rest) R tR lemma79Count)
    (hprefix :
      TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P R first Γ rest) :
    tR < P :=
  h.tR_ltP_of_all_stop_ltP hprefix.all_stop_ltP

/--
Transport the actual-run `t_R` accessor to an identified finite prefix.

This is the endpoint-safe form needed when Tao's run has at least `R` stops:
the constructed prefix is `steps.take R`, not necessarily the whole terminal
run.
-/
theorem prefix_tR_eq_of_take_eq
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n J P R first tR lemma79Count : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {Γ : TaoSection7Triangle}
    {steps rest : List (ℕ × TaoSection7Triangle)}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (htake : steps.take R = (first, Γ) :: rest) :
    TaoSection7Case3SourceStoppingRun.tR?
        ((first, Γ) :: rest) R = some tR := by
  have htR_take :
      TaoSection7Case3SourceStoppingRun.tR? (steps.take R) R =
        some tR :=
    TaoSection7Case3SourceStoppingRun.tR?_take_eq_of_tR? h.tR_eq
  simpa [htake] using htR_take

/--
Endpoint-window extractor from a prefix identified as `steps.take R`.

Unlike `tR_ltP_of_prefixRInputs`, this does not require the actual terminal
run to be exactly the constructed prefix.  It only uses the first `R` stops of
the full actual run.
-/
theorem tR_ltP_of_prefixRInputs_take_eq
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J P R first tR lemma79Count : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {Γ : TaoSection7Triangle}
    {steps rest : List (ℕ × TaoSection7Triangle)}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P
        steps R tR lemma79Count)
    (htake : steps.take R = (first, Γ) :: rest)
    (hprefix :
      TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P R first Γ rest) :
    tR < P := by
  have htR_prefix :
      TaoSection7Case3SourceStoppingRun.tR?
          ((first, Γ) :: rest) R = some tR :=
    h.prefix_tR_eq_of_take_eq htake
  rcases hprefix.hasTWithinWindow h.R_pos with ⟨t, htR, htP⟩
  rw [htR_prefix] at htR
  cases htR
  exact htP

end TaoSection7Case3ActualRunSourceIdentity

/--
Variant of the actual-run low-white subset bridge whose endpoint half is
derived from the checked finite R-prefix input package.

This is the source-iteration-shaped successor of the raw
all-stops-below-`P` bridge.  It still leaves the many-white lower bound to the
future Lemma 7.9/Markov producer.
-/
theorem taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_prefixRInputs
    {Ω : Type*}
    {sourceAt : Ω → ℕ → TaoSection7Point}
    {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {black : Ω → TaoSection7Point → Prop}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {Accepts : Ω → ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {family : Set TaoSection7Triangle}
    {n J P R threshold : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {first : Ω → ℕ}
    {Γ : Ω → TaoSection7Triangle}
    {rest : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count : Ω → ℕ}
    {EStarUsed FSlack : Set Ω}
    (hidentity :
      ∀ ω : Ω,
        TaoSection7Case3ActualRunSourceIdentity
          (sourceAt ω) (restart ω) (W ω) (black ω) (pointAt ω) family
          n J xi epsilon P ((first ω, Γ ω) :: rest ω) R
          (tR ω) (lemma79Count ω))
    (hprefix :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        TaoSection7Case3PrefixRInputs
          (black ω) family (pointAt ω) (Accepts ω) P R
          (first ω) (Γ ω) (rest ω))
    (hmany :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        threshold < lemma79Count ω) :
    taoSection7Case3LowWhiteEvent W P threshold ⊆ EStarUsed ∪ FSlack := by
  refine
    taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity
      (hidentity := hidentity) ?_
  intro ω hnotE hnotF
  exact
    ⟨(hidentity ω).tR_ltP_of_prefixRInputs
        (hprefix ω hnotE hnotF),
      hmany ω hnotE hnotF⟩

/--
Take-prefix variant of the actual-run low-white subset bridge.

The actual run may have more than `R` stops.  Outside the exceptional sets the
caller identifies the first `R` stops as the checked finite prefix via
`steps.take R`, and this theorem derives the endpoint half from that prefix
without asserting terminality at the prefix.
-/
theorem taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_prefixRInputs_take_eq
    {Ω : Type*}
    {sourceAt : Ω → ℕ → TaoSection7Point}
    {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {black : Ω → TaoSection7Point → Prop}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {Accepts : Ω → ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {family : Set TaoSection7Triangle}
    {n J P R threshold : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps rest : Ω → List (ℕ × TaoSection7Triangle)}
    {first : Ω → ℕ}
    {Γ : Ω → TaoSection7Triangle}
    {tR lemma79Count : Ω → ℕ}
    {EStarUsed FSlack : Set Ω}
    (hidentity :
      ∀ ω : Ω,
        TaoSection7Case3ActualRunSourceIdentity
          (sourceAt ω) (restart ω) (W ω) (black ω) (pointAt ω) family
          n J xi epsilon P (steps ω) R
          (tR ω) (lemma79Count ω))
    (htake :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        (steps ω).take R = (first ω, Γ ω) :: rest ω)
    (hprefix :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        TaoSection7Case3PrefixRInputs
          (black ω) family (pointAt ω) (Accepts ω) P R
          (first ω) (Γ ω) (rest ω))
    (hmany :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        threshold < lemma79Count ω) :
    taoSection7Case3LowWhiteEvent W P threshold ⊆ EStarUsed ∪ FSlack := by
  refine
    taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity
      (hidentity := hidentity) ?_
  intro ω hnotE hnotF
  exact
    ⟨(hidentity ω).tR_ltP_of_prefixRInputs_take_eq
        (htake ω hnotE hnotF) (hprefix ω hnotE hnotF),
      hmany ω hnotE hnotF⟩

/--
Tail list for an indexed sequence of stopping times and triangles.

The element at offset `k + m + 1` is recorded as the next stopping pair.  This
is an assembler for already-supplied encounter steps, not a source producer.
-/
def taoSection7Case3IndexedEncounterTail
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle) :
    ℕ → ℕ → List (ℕ × TaoSection7Triangle)
  | _, 0 => []
  | k, n + 1 =>
      (t (k + 1), tri (k + 1)) ::
        taoSection7Case3IndexedEncounterTail t tri (k + 1) n

theorem taoSection7Case3IndexedEncounterTail_length
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle) :
    ∀ k n : ℕ,
      (taoSection7Case3IndexedEncounterTail t tri k n).length = n := by
  intro k n
  induction n generalizing k with
  | zero =>
      simp [taoSection7Case3IndexedEncounterTail]
  | succ n ih =>
      simp [taoSection7Case3IndexedEncounterTail, ih]

theorem taoSection7Case3_recursiveEncounterChain_of_indexedTail
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P : ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle) :
    ∀ k n : ℕ,
      (∀ i : ℕ, k ≤ i → i < k + n →
        TaoSection7Case3EncounterStep
          black family pointAt Accepts P (t i) (tri i) (tri (i + 1))
            (t (i + 1))) →
      TaoSection7Case3RecursiveEncounterChain
        black family pointAt Accepts P (t k) (tri k)
          (taoSection7Case3IndexedEncounterTail t tri k n) := by
  intro k n
  induction n generalizing k with
  | zero =>
      intro _hstep
      simpa [taoSection7Case3IndexedEncounterTail] using
        TaoSection7Case3RecursiveEncounterChain.nil
          (black := black) (family := family) (pointAt := pointAt)
          (Accepts := Accepts) (P := P) (t k) (tri k)
  | succ n ih =>
      intro hstep
      have hhead :
          TaoSection7Case3EncounterStep
            black family pointAt Accepts P (t k) (tri k) (tri (k + 1))
              (t (k + 1)) :=
        hstep k le_rfl (by omega)
      have htail :
          TaoSection7Case3RecursiveEncounterChain
            black family pointAt Accepts P (t (k + 1)) (tri (k + 1))
              (taoSection7Case3IndexedEncounterTail t tri (k + 1) n) :=
        ih (k + 1) (by
          intro i hki hi
          exact hstep i (by omega) (by omega))
      simpa [taoSection7Case3IndexedEncounterTail] using
        TaoSection7Case3RecursiveEncounterChain.cons hhead htail

theorem taoSection7Case3_hasAtLeast_cons_indexedTail
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (k Rtail : ℕ) :
    TaoSection7Case3SourceStoppingRun.HasAtLeast
      ((t k, tri k) ::
        taoSection7Case3IndexedEncounterTail t tri k Rtail)
      (Rtail + 1) := by
  simp [TaoSection7Case3SourceStoppingRun.HasAtLeast,
    TaoSection7Case3SourceStoppingRun.r,
    taoSection7Case3IndexedEncounterTail_length]

theorem taoSection7Case3_tR?_cons_indexedTail_last
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle) :
    ∀ k Rtail : ℕ,
      TaoSection7Case3SourceStoppingRun.tR?
          ((t k, tri k) ::
            taoSection7Case3IndexedEncounterTail t tri k Rtail)
          (Rtail + 1) =
        some (t (k + Rtail)) := by
  intro k Rtail
  induction Rtail generalizing k with
  | zero =>
      simp [TaoSection7Case3SourceStoppingRun.tR?]
  | succ Rtail ih =>
      have hidx : k + (Rtail + 1) = k + 1 + Rtail := by omega
      simp [taoSection7Case3IndexedEncounterTail,
        TaoSection7Case3SourceStoppingRun.tR?, ih (k + 1), hidx]

theorem taoSection7Case3StoppingLast?_cons_indexedTail
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle) :
    ∀ k Rtail : ℕ,
      TaoSection7Case3StoppingLast?
          ((t k, tri k) ::
            taoSection7Case3IndexedEncounterTail t tri k Rtail) =
        some (t (k + Rtail), tri (k + Rtail)) := by
  intro k Rtail
  induction Rtail generalizing k with
  | zero =>
      simp [taoSection7Case3IndexedEncounterTail,
        TaoSection7Case3StoppingLast?]
  | succ Rtail ih =>
      have hidx : k + (Rtail + 1) = k + 1 + Rtail := by omega
      simp [taoSection7Case3IndexedEncounterTail,
        TaoSection7Case3StoppingLast?, ih (k + 1), hidx]

theorem taoSection7Case3_prefixRInputs_of_indexedEncounterTail
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {P : ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    {Rtail : ℕ}
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family (t 0) (tri 0))
    (hfirst_ltP : t 0 < P)
    (hsteps :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3EncounterStep
          black family pointAt Accepts P (t i) (tri i) (tri (i + 1))
            (t (i + 1))) :
    TaoSection7Case3PrefixRInputs
      black family pointAt Accepts P (Rtail + 1) (t 0) (tri 0)
        (taoSection7Case3IndexedEncounterTail t tri 0 Rtail) := by
  refine
    { initial := hinit
      first_ltP := hfirst_ltP
      encounter_chain := ?_
      hasAtLeast := ?_ }
  · exact
      taoSection7Case3_recursiveEncounterChain_of_indexedTail
        (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (P := P) t tri 0 Rtail
        (by
          intro i _h0 hi
          exact hsteps i (by simpa using hi))
  · exact taoSection7Case3_hasAtLeast_cons_indexedTail t tri 0 Rtail

theorem taoSection7Case3_prefixRInputs_and_rebasedStates_of_indexedFirstHitSourceProvenance
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (candidate : ℕ → ℕ)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family (t 0) (tri 0))
    (hfirst_ltP : t 0 < P)
    (hfull :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FullWindowSourcePathData
          W pointAt n J A xi epsilon P threshold (t i)
          (j i) (s i) (pre i) (pres i))
    (hsrc :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FirstHitSourceProvenance
          black family pointAt (j i) (s i) (pre i) (pres i)
          P (t i) (tri i) (tri (i + 1)) (candidate i) (t (i + 1)))
    (hroom_next :
      ∀ i : ℕ, i < Rtail →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound
            (taoSection7Case3ExitGapBound A) threshold) P (t (i + 1)))
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (haccept :
      ∀ i : ℕ, i < Rtail →
        Accepts (t i) (tri i) (t (i + 1)) (tri (i + 1))) :
    TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P (Rtail + 1) (t 0) (tri 0)
        (taoSection7Case3IndexedEncounterTail t tri 0 Rtail) ∧
      ∀ i : ℕ, i < Rtail →
        ∃ before : List (List ℕ), ∃ next : List ℕ,
          ∃ after : List (List ℕ),
            pres i = before ++ next :: after ∧
            before.length + 1 = t (i + 1) - t i ∧
            TaoSection7Case3EncounterStep
              black family pointAt Accepts P (t i) (tri i) (tri (i + 1))
                (t (i + 1)) ∧
            TaoSection7Case3FullWindowSourcePathData
              W pointAt n J A xi epsilon P threshold (t (i + 1))
              (taoSection7SourceBlockStartJFrom (j i) (pre i :: before))
              (taoSection7SourceBlockStartSFrom (s i) (pre i :: before))
              next after := by
  constructor
  · exact
      taoSection7Case3_prefixRInputs_of_indexedEncounterTail
        (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (P := P) t tri
        (Rtail := Rtail) hinit hfirst_ltP
        (by
          intro i hi
          exact (hsrc i hi).to_encounterStep (haccept i hi))
  · intro i hi
    exact
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathData_of_firstHitSourceProvenance
        (hfull := hfull i hi) (hsrc := hsrc i hi)
        (hroom_first := hroom_next i hi) (hfacts := hfacts)
        (haccept := haccept i hi)

theorem taoSection7Case3_prefixRInputs_and_rebasedStatesWithGap_of_indexedFirstHitSourceProvenance
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ} {gapBound : ℕ → ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (candidate : ℕ → ℕ)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family (t 0) (tri 0))
    (hfirst_ltP : t 0 < P)
    (hfull :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i))
    (hsrc :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FirstHitSourceProvenance
          black family pointAt (j i) (s i) (pre i) (pres i)
          P (t i) (tri i) (tri (i + 1)) (candidate i) (t (i + 1)))
    (hroom_next :
      ∀ i : ℕ, i < Rtail →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold)
          P (t (i + 1)))
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (haccept :
      ∀ i : ℕ, i < Rtail →
        Accepts (t i) (tri i) (t (i + 1)) (tri (i + 1))) :
    TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P (Rtail + 1) (t 0) (tri 0)
        (taoSection7Case3IndexedEncounterTail t tri 0 Rtail) ∧
      ∀ i : ℕ, i < Rtail →
        ∃ before : List (List ℕ), ∃ next : List ℕ,
          ∃ after : List (List ℕ),
            pres i = before ++ next :: after ∧
            before.length + 1 = t (i + 1) - t i ∧
            TaoSection7Case3EncounterStep
              black family pointAt Accepts P (t i) (tri i) (tri (i + 1))
                (t (i + 1)) ∧
            TaoSection7Case3FullWindowSourcePathDataWithGap
              W pointAt n J xi epsilon P threshold (t (i + 1)) gapBound
              (taoSection7SourceBlockStartJFrom (j i) (pre i :: before))
              (taoSection7SourceBlockStartSFrom (s i) (pre i :: before))
              next after := by
  constructor
  · exact
      taoSection7Case3_prefixRInputs_of_indexedEncounterTail
        (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (P := P) t tri
        (Rtail := Rtail) hinit hfirst_ltP
        (by
          intro i hi
          exact (hsrc i hi).to_encounterStep (haccept i hi))
  · intro i hi
    exact
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
        (hfull := hfull i hi) (hsrc := hsrc i hi)
        (hroom_first := hroom_next i hi) (hfacts := hfacts)
        (haccept := haccept i hi)

theorem taoSection7Case3_prefixRInputs_and_stateInvariant_of_indexedSourceStateUpdates
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family (t 0) (tri 0))
    (hfirst_ltP : t 0 < P)
    (hstate0 :
      TaoSection7Case3FullWindowSourcePathData
        W pointAt n J A xi epsilon P threshold (t 0)
        (j 0) (s 0) (pre 0) (pres 0))
    (hupdates :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3EncounterStep
          black family pointAt Accepts P (t i) (tri i) (tri (i + 1))
            (t (i + 1)) ∧
        TaoSection7Case3FullWindowSourcePathData
          W pointAt n J A xi epsilon P threshold (t (i + 1))
          (j (i + 1)) (s (i + 1)) (pre (i + 1)) (pres (i + 1))) :
    TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P (Rtail + 1) (t 0) (tri 0)
        (taoSection7Case3IndexedEncounterTail t tri 0 Rtail) ∧
      ∀ i : ℕ, i ≤ Rtail →
        TaoSection7Case3FullWindowSourcePathData
          W pointAt n J A xi epsilon P threshold (t i)
          (j i) (s i) (pre i) (pres i) := by
  constructor
  · exact
      taoSection7Case3_prefixRInputs_of_indexedEncounterTail
        (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (P := P) t tri
        (Rtail := Rtail) hinit hfirst_ltP
        (by
          intro i hi
          exact (hupdates i hi).1)
  · intro i hi
    cases i with
    | zero =>
        exact hstate0
    | succ k =>
        have hk : k < Rtail := by omega
        simpa using (hupdates k hk).2

theorem taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_indexedSourceStateUpdates
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ} {gapBound : ℕ → ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family (t 0) (tri 0))
    (hfirst_ltP : t 0 < P)
    (hstate0 :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold (t 0) gapBound
        (j 0) (s 0) (pre 0) (pres 0))
    (hupdates :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3EncounterStep
          black family pointAt Accepts P (t i) (tri i) (tri (i + 1))
            (t (i + 1)) ∧
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t (i + 1)) gapBound
          (j (i + 1)) (s (i + 1)) (pre (i + 1)) (pres (i + 1))) :
    TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P (Rtail + 1) (t 0) (tri 0)
        (taoSection7Case3IndexedEncounterTail t tri 0 Rtail) ∧
      ∀ i : ℕ, i ≤ Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i) := by
  constructor
  · exact
      taoSection7Case3_prefixRInputs_of_indexedEncounterTail
        (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (P := P) t tri
        (Rtail := Rtail) hinit hfirst_ltP
        (by
          intro i hi
          exact (hupdates i hi).1)
  · intro i hi
    cases i with
    | zero =>
        exact hstate0
    | succ k =>
        have hk : k < Rtail := by omega
        simpa using (hupdates k hk).2

/--
One indexed source-state update after rebasing at the next first hit.

The future source-derived recurrence producer should fill this packet for each
`i`.  The equalities make explicit that the next indexed state is exactly the
rebased source block returned by the one-step first-hit construction.
-/
structure TaoSection7Case3IndexedRebasedSourceUpdateWithGap
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (i : ℕ) : Type where
  before : List (List ℕ)
  next : List ℕ
  after : List (List ℕ)
  split : pres i = before ++ next :: after
  j_next :
    j (i + 1) =
      taoSection7SourceBlockStartJFrom (j i) (pre i :: before)
  s_next :
    s (i + 1) =
      taoSection7SourceBlockStartSFrom (s i) (pre i :: before)
  pre_next : pre (i + 1) = next
  pres_next : pres (i + 1) = after
  encounter :
    TaoSection7Case3EncounterStep
      black family pointAt Accepts P (t i) (tri i) (tri (i + 1))
        (t (i + 1))
  rebased :
    TaoSection7Case3FullWindowSourcePathDataWithGap
      W pointAt n J xi epsilon P threshold (t (i + 1)) gapBound
      (taoSection7SourceBlockStartJFrom (j i) (pre i :: before))
      (taoSection7SourceBlockStartSFrom (s i) (pre i :: before))
      next after

namespace TaoSection7Case3IndexedRebasedSourceUpdateWithGap

theorem to_sourceStateUpdate
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    {t : ℕ → ℕ} {tri : ℕ → TaoSection7Triangle}
    {j : ℕ → ℕ+} {s : ℕ → ℕ}
    {pre : ℕ → List ℕ} {pres : ℕ → List (List ℕ)}
    {i : ℕ}
    (hupdate :
      TaoSection7Case3IndexedRebasedSourceUpdateWithGap
        (W := W) (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) t tri j s pre pres i) :
    TaoSection7Case3EncounterStep
        black family pointAt Accepts P (t i) (tri i) (tri (i + 1))
          (t (i + 1)) ∧
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold (t (i + 1)) gapBound
        (j (i + 1)) (s (i + 1)) (pre (i + 1)) (pres (i + 1)) := by
  constructor
  · exact hupdate.encounter
  · rw [hupdate.j_next, hupdate.s_next, hupdate.pre_next,
      hupdate.pres_next]
    exact hupdate.rebased

end TaoSection7Case3IndexedRebasedSourceUpdateWithGap

/--
Existential one-step rebased source update, before committing to indexed
successor arrays.

This is the local packet shape produced from the current full-window source
state: it chooses the first hit, source split, and rebased successor state.
-/
structure TaoSection7Case3OneStepRebasedSourceUpdateWithGap
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ} {gapBound : ℕ → ℕ}
    (j : ℕ+) (s : ℕ) (pre : List ℕ) (pres : List (List ℕ))
    (old : TaoSection7Triangle) : Type where
  candidate : ℕ
  first : ℕ
  triangle : TaoSection7Triangle
  before : List (List ℕ)
  next : List ℕ
  after : List (List ℕ)
  split : pres = before ++ next :: after
  index : before.length + 1 = first - q
  source :
    TaoSection7Case3FirstHitSourceProvenance
      black family pointAt j s pre pres P q old triangle candidate first
  encounter :
    TaoSection7Case3EncounterStep
      black family pointAt Accepts P q old triangle first
  rebased :
    TaoSection7Case3FullWindowSourcePathDataWithGap
      W pointAt n J xi epsilon P threshold first gapBound
      (taoSection7SourceBlockStartJFrom j (pre :: before))
      (taoSection7SourceBlockStartSFrom s (pre :: before))
      next after

namespace TaoSection7Case3OneStepRebasedSourceUpdateWithGap

theorem q_lt_first
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ} {gapBound : ℕ → ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold) (q := q)
        (gapBound := gapBound) j s pre pres old) :
    q < hupdate.first :=
  hupdate.source.first_hit.1

theorem first_ltP
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q : ℕ} {gapBound : ℕ → ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold) (q := q)
        (gapBound := gapBound) j s pre pres old) :
    hupdate.first < P :=
  hupdate.source.first_ltP

theorem pair_eq_of_pairwiseDisjoint_stoppingTransition
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold q first : ℕ} {gapBound : ℕ → ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old Γ : TaoSection7Triangle}
    (hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold) (q := q)
        (gapBound := gapBound) j s pre pres old)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hstep :
      TaoSection7Case3StoppingTransition pointAt family q old first Γ) :
    (first, Γ) = (hupdate.first, hupdate.triangle) :=
  TaoSection7Case3StoppingTransition.pair_eq_of_pairwiseDisjoint
    hpair hstep hupdate.source.to_stoppingTransition

def to_indexedRebasedSourceUpdateWithGap
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    {t : ℕ → ℕ} {tri : ℕ → TaoSection7Triangle}
    {j : ℕ → ℕ+} {s : ℕ → ℕ}
    {pre : ℕ → List ℕ} {pres : ℕ → List (List ℕ)}
    {i : ℕ}
    (hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold) (q := t i)
        (gapBound := gapBound) (j i) (s i) (pre i) (pres i) (tri i))
    (ht_next : t (i + 1) = hupdate.first)
    (htri_next : tri (i + 1) = hupdate.triangle)
    (hj_next :
      j (i + 1) =
        taoSection7SourceBlockStartJFrom (j i) (pre i :: hupdate.before))
    (hs_next :
      s (i + 1) =
        taoSection7SourceBlockStartSFrom (s i) (pre i :: hupdate.before))
    (hpre_next : pre (i + 1) = hupdate.next)
    (hpres_next : pres (i + 1) = hupdate.after) :
    TaoSection7Case3IndexedRebasedSourceUpdateWithGap
      (W := W) (black := black) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := gapBound) t tri j s pre pres i := by
  refine
    { before := hupdate.before
      next := hupdate.next
      after := hupdate.after
      split := hupdate.split
      j_next := hj_next
      s_next := hs_next
      pre_next := hpre_next
      pres_next := hpres_next
      encounter := ?_
      rebased := ?_ }
  · simpa [ht_next, htri_next] using hupdate.encounter
  · simpa [ht_next] using hupdate.rebased

end TaoSection7Case3OneStepRebasedSourceUpdateWithGap

/--
Existential one-step packet producer from the current `WithGap` state.

This chooses the first hit and split witnesses instead of taking indexed
`hsplit`/successor-state equalities as premises.
-/
theorem taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_of_fullWindowSourcePathDataWithGap
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ old →
        Accepts q old first Γ) :
    Nonempty
      (TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := q) (gapBound := gapBound)
        j s pre pres old) := by
  rcases
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_fullWindowSourcePathDataWithGap
        (W := W) (pointAt := pointAt) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (P := P) (threshold := threshold) (q := q) (j := j)
        (s := s) (pre := pre) (pres := pres) (old := old)
        hfull hscale hlow hroom hactive hcover hroom_next hfacts
        haccept with
    ⟨candidate, first, Γ, before, next, after, hsplit, hidx, hsrc,
      hstep, hrebase⟩
  exact
    ⟨{ candidate := candidate
       first := first
       triangle := Γ
       before := before
       next := next
       after := after
       split := hsplit
       index := hidx
       source := hsrc
       encounter := hstep
       rebased := hrebase }⟩

/--
One-step packet producer with selected-offset membership from the full local
first-hit envelope.

The proof keeps the later-search candidate window membership long enough to
combine it with `hsrc.first_le_candidate`.  This avoids replacing the
selected offset by the later-search block or assuming the broad range premise
`∀ first, q < first → first < P → first ∈ allowed`.
-/
theorem taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace allowed (q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold q - (q + 1)))
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ old →
        Accepts q old first Γ) :
    ∃ hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := q) (gapBound := gapBound)
        j s pre pres old,
      hupdate.first ∈ allowed := by
  have hdata :
      TaoSection7Case3SourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres :=
    hfull.to_sourcePathDataWithGap hroom
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_scale_coverage
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive hcover hfull.point_window with
    ⟨candidate, _pivot, hpivot, first, Γ, hsrc⟩
  have hallowed : first ∈ allowed :=
    TaoSection7Case3AllowedBlockTrace.first_mem_of_le_laterSearch_candidate
      (hblock := hblock) (hcandidate := hpivot.mem_later_window)
      (hqfirst := hsrc.first_hit.1)
      (hfirst_le_candidate := hsrc.first_le_candidate)
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first :=
    hroom_next first hsrc.first_hit.1 hsrc.first_ltP
  have haccept_step : Accepts q old first Γ :=
    haccept first Γ hsrc.first_ltP hsrc.first_black hsrc.first_hit
      hsrc.new_mem_family hsrc.new_mem hsrc.new_ne_old
  rcases
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
        (hfull := hfull) (hsrc := hsrc)
        (hroom_first := hroom_first) (hfacts := hfacts)
        (haccept := haccept_step) with
    ⟨before, next, after, hsplit, hidx, hstep, hrebase⟩
  exact
    ⟨{ candidate := candidate
       first := first
       triangle := Γ
       before := before
       next := next
       after := after
       split := hsplit
       index := hidx
       source := hsrc
       encounter := hstep
       rebased := hrebase },
      hallowed⟩

/--
Direct-room selected-offset version of the one-step packet producer.

This keeps the selected first-hit membership proof and uses it to request room
only for that selected offset, rather than a universal callback for every
future point below `P`.
-/
theorem taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap_room
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_selected :
      ∀ first : ℕ, first ∈ allowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace allowed (q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold q - (q + 1)))
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ old →
        Accepts q old first Γ) :
    ∃ hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := q) (gapBound := gapBound)
        j s pre pres old,
      hupdate.first ∈ allowed := by
  have hdata :
      TaoSection7Case3SourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres :=
    hfull.to_sourcePathDataWithGap hroom
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_scale_coverage
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive hcover hfull.point_window with
    ⟨candidate, _pivot, hpivot, first, Γ, hsrc⟩
  have hallowed : first ∈ allowed :=
    TaoSection7Case3AllowedBlockTrace.first_mem_of_le_laterSearch_candidate
      (hblock := hblock) (hcandidate := hpivot.mem_later_window)
      (hqfirst := hsrc.first_hit.1)
      (hfirst_le_candidate := hsrc.first_le_candidate)
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first :=
    hroom_selected first hallowed
  have haccept_step : Accepts q old first Γ :=
    haccept first Γ hsrc.first_ltP hsrc.first_black hsrc.first_hit
      hsrc.new_mem_family hsrc.new_mem hsrc.new_ne_old
  rcases
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
        (hfull := hfull) (hsrc := hsrc)
        (hroom_first := hroom_first) (hfacts := hfacts)
        (haccept := haccept_step) with
    ⟨before, next, after, hsplit, hidx, hstep, hrebase⟩
  exact
    ⟨{ candidate := candidate
       first := first
       triangle := Γ
       before := before
       next := next
       after := after
       split := hsplit
       index := hidx
       source := hsrc
       encounter := hstep
       rebased := hrebase },
      hallowed⟩

/--
Direct-room one-step packet producer with transition-shaped acceptance.

The acceptance premise is tied to the selected stopping transition produced by
the first-hit source packet, rather than a broad callback over arbitrary future
`first, Γ` data.
-/
theorem taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap_room_accept
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_selected :
      ∀ first : ℕ, first ∈ allowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace allowed (q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold q - (q + 1)))
    (haccept_step :
      ∀ {first : ℕ} {Γ : TaoSection7Triangle},
        first < P →
        TaoSection7Case3StoppingTransition pointAt family q old first Γ →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        Accepts q old first Γ) :
    ∃ hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := q) (gapBound := gapBound)
        j s pre pres old,
      hupdate.first ∈ allowed := by
  have hdata :
      TaoSection7Case3SourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres :=
    hfull.to_sourcePathDataWithGap hroom
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_scale_coverage
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive hcover hfull.point_window with
    ⟨candidate, _pivot, hpivot, first, Γ, hsrc⟩
  have hallowed : first ∈ allowed :=
    TaoSection7Case3AllowedBlockTrace.first_mem_of_le_laterSearch_candidate
      (hblock := hblock) (hcandidate := hpivot.mem_later_window)
      (hqfirst := hsrc.first_hit.1)
      (hfirst_le_candidate := hsrc.first_le_candidate)
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first :=
    hroom_selected first hallowed
  have haccept_selected : Accepts q old first Γ :=
    haccept_step (first := first) (Γ := Γ) hsrc.first_ltP
      hsrc.to_stoppingTransition hsrc.first_black
  rcases
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
        (hfull := hfull) (hsrc := hsrc)
        (hroom_first := hroom_first) (hfacts := hfacts)
        (haccept := haccept_selected) with
    ⟨before, next, after, hsplit, hidx, hstep, hrebase⟩
  exact
    ⟨{ candidate := candidate
       first := first
       triangle := Γ
       before := before
       next := next
       after := after
       split := hsplit
       index := hidx
       source := hsrc
       encounter := hstep
       rebased := hrebase },
      hallowed⟩

/--
Direct-room one-step packet producer with source-provenance-shaped acceptance.

The acceptance premise consumes the selected first-hit source packet itself,
before it is collapsed to a stopping transition or encounter step.
-/
theorem taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap_room_acceptSource
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_selected :
      ∀ first : ℕ, first ∈ allowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace allowed (q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold q - (q + 1)))
    (haccept_src :
      ∀ {candidate first : ℕ} {Γ : TaoSection7Triangle},
        TaoSection7Case3FirstHitSourceProvenance
          (taoSection7SourceBlackInDomain n xi epsilon J)
          family pointAt j s pre pres P q old Γ candidate first →
        Accepts q old first Γ) :
    ∃ hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := q) (gapBound := gapBound)
        j s pre pres old,
      hupdate.first ∈ allowed := by
  have hdata :
      TaoSection7Case3SourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres :=
    hfull.to_sourcePathDataWithGap hroom
  rcases
      taoSection7Case3_exists_firstHitSourceProvenance_of_sourcePathData_scale_coverage
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive hcover hfull.point_window with
    ⟨candidate, _pivot, hpivot, first, Γ, hsrc⟩
  have hallowed : first ∈ allowed :=
    TaoSection7Case3AllowedBlockTrace.first_mem_of_le_laterSearch_candidate
      (hblock := hblock) (hcandidate := hpivot.mem_later_window)
      (hqfirst := hsrc.first_hit.1)
      (hfirst_le_candidate := hsrc.first_le_candidate)
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first :=
    hroom_selected first hallowed
  have haccept_selected : Accepts q old first Γ := haccept_src hsrc
  rcases
      taoSection7Case3_exists_encounterStep_and_rebasedFullWindowSourcePathDataWithGap_of_firstHitSourceProvenance
        (hfull := hfull) (hsrc := hsrc)
        (hroom_first := hroom_first) (hfacts := hfacts)
        (haccept := haccept_selected) with
    ⟨before, next, after, hsplit, hidx, hstep, hrebase⟩
  exact
    ⟨{ candidate := candidate
       first := first
       triangle := Γ
       before := before
       next := next
       after := after
       split := hsplit
       index := hidx
       source := hsrc
       encounter := hstep
       rebased := hrebase },
      hallowed⟩

/--
No-budget active-state version of the existential one-step packet producer.

This is the recursive source-state shape: it carries the successor room and
active-triangle facts without requiring the fixed-start budget premise
`q ∈ Icc start (start + threshold)`.
-/
theorem taoSection7Case3_exists_oneStepActiveRebasedSourceUpdateWithGap_noBudget_of_fullWindowSourcePathDataWithGap
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (hallowed_first :
      ∀ first : ℕ, q < first → first < P → first ∈ allowed)
    (hnotLarge :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ old →
        Accepts q old first Γ) :
    ∃ hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := q) (gapBound := gapBound)
        j s pre pres old,
      taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold)
          P hupdate.first ∧
        TaoSection7Case3ActiveTriangleAtWithBound
          family pointAt bound hupdate.first hupdate.triangle := by
  rcases
      taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_of_fullWindowSourcePathDataWithGap
        (W := W) (pointAt := pointAt) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres) (old := old)
        hfull hscale hlow hroom hactive hcover hroom_next hfacts
        haccept with
    ⟨hupdate⟩
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold)
        P hupdate.first :=
    hroom_next hupdate.first hupdate.q_lt_first hupdate.first_ltP
  have hallowed : hupdate.first ∈ allowed :=
    hallowed_first hupdate.first hupdate.q_lt_first hupdate.first_ltP
  have hsmall : hupdate.triangle.size < bound hupdate.first :=
    taoSection7Case3_triangle_size_lt_of_not_large_union
      (pointAt := pointAt) (family := family) (allowed := allowed)
      (bound := bound) hnotLarge hallowed hupdate.source.new_mem_family
      hupdate.source.new_mem
  refine ⟨hupdate, hroom_first, ?_⟩
  exact
    { old_mem_family := hupdate.source.new_mem_family
      pivot_mem := hupdate.source.new_mem
      small_size := hsmall }

/--
Selected-update active successor facts for the no-budget Case 3 recurrence.

Unlike the broader existential producer above, this consumes membership of
the selected update's own first-hit offset in the used/allowed set.  This is
the source-faithful socket for the later `E_*` provenance step: callers should
prove `hupdate.first ∈ allowed` from the selected pivot/used-event data, not
from an unrelated later-search block.
-/
theorem taoSection7Case3_oneStepActiveFactsWithGap_of_selectedAllowed
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold) (q := q)
        (gapBound := gapBound) j s pre pres old)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hallowed : hupdate.first ∈ allowed)
    (hnotLarge :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound) :
    taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold)
        P hupdate.first ∧
      TaoSection7Case3ActiveTriangleAtWithBound
        family pointAt bound hupdate.first hupdate.triangle := by
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold)
        P hupdate.first :=
    hroom_next hupdate.first hupdate.q_lt_first hupdate.first_ltP
  have hsmall : hupdate.triangle.size < bound hupdate.first :=
    taoSection7Case3_triangle_size_lt_of_not_large_union
      (pointAt := pointAt) (family := family) (allowed := allowed)
      (bound := bound) hnotLarge hallowed hupdate.source.new_mem_family
      hupdate.source.new_mem
  exact
    ⟨hroom_first,
      { old_mem_family := hupdate.source.new_mem_family
        pivot_mem := hupdate.source.new_mem
        small_size := hsmall }⟩

/--
Direct-room variant of the selected-update active successor facts.

This is the narrower socket used once the selected first-hit offset is known:
callers only need room at `hupdate.first`, not a universal successor-room
callback for every future first.
-/
theorem taoSection7Case3_oneStepActiveFactsWithGap_of_selectedAllowed_room
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    {P threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold) (q := q)
        (gapBound := gapBound) j s pre pres old)
    (hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold)
        P hupdate.first)
    (hallowed : hupdate.first ∈ allowed)
    (hnotLarge :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound) :
    taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold)
        P hupdate.first ∧
      TaoSection7Case3ActiveTriangleAtWithBound
        family pointAt bound hupdate.first hupdate.triangle := by
  have hsmall : hupdate.triangle.size < bound hupdate.first :=
    taoSection7Case3_triangle_size_lt_of_not_large_union
      (pointAt := pointAt) (family := family) (allowed := allowed)
      (bound := bound) hnotLarge hallowed hupdate.source.new_mem_family
      hupdate.source.new_mem
  exact
    ⟨hroom_first,
      { old_mem_family := hupdate.source.new_mem_family
        pivot_mem := hupdate.source.new_mem
        small_size := hsmall }⟩

/--
Current source-state payload for the no-budget Case 3 active recurrence.

The data fields are exactly the projections that will become the indexed
arrays `t`, `tri`, `j`, `s`, `pre`, and `pres` in the finite trace.
-/
structure TaoSection7Case3ActiveSourceStateWithGap
    (W : ℕ → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (bound : ℕ → ℝ)
    (n J : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (P threshold : ℕ) (gapBound : ℕ → ℕ) : Type where
  q : ℕ
  old : TaoSection7Triangle
  j : ℕ+
  s : ℕ
  pre : List ℕ
  pres : List (List ℕ)
  full :
    TaoSection7Case3FullWindowSourcePathDataWithGap
      W pointAt n J xi epsilon P threshold q gapBound j s pre pres
  room :
    taoSection7Case3ExitRoom
      (taoSection7Case3LaterSearchBound gapBound threshold) P q
  active :
    TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old

/--
A chosen no-budget active step out of one source state.

This records the single packet selected by the local producer, together with
the successor room and active-triangle facts that become the next state's
proof fields.
-/
structure TaoSection7Case3ChosenActiveStepWithGap
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound) :
    Type where
  update :
    TaoSection7Case3OneStepRebasedSourceUpdateWithGap
      (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
      (family := family) (pointAt := pointAt) (Accepts := Accepts)
      (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
      (threshold := threshold) (q := st.q) (gapBound := gapBound)
      st.j st.s st.pre st.pres st.old
  room_next :
    taoSection7Case3ExitRoom
      (taoSection7Case3LaterSearchBound gapBound threshold) P update.first
  active_next :
    TaoSection7Case3ActiveTriangleAtWithBound
      family pointAt bound update.first update.triangle

namespace TaoSection7Case3ChosenActiveStepWithGap

def nextState
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    {st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound}
    (hstep :
      TaoSection7Case3ChosenActiveStepWithGap
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (gapBound := gapBound) st) :
    TaoSection7Case3ActiveSourceStateWithGap
      W family pointAt bound n J xi epsilon P threshold gapBound :=
  { q := hstep.update.first
    old := hstep.update.triangle
    j := taoSection7SourceBlockStartJFrom st.j
      (st.pre :: hstep.update.before)
    s := taoSection7SourceBlockStartSFrom st.s
      (st.pre :: hstep.update.before)
    pre := hstep.update.next
    pres := hstep.update.after
    full := hstep.update.rebased
    room := hstep.room_next
    active := hstep.active_next }

end TaoSection7Case3ChosenActiveStepWithGap

/--
Build a chosen active step from a concrete one-step update whose selected
first-hit offset is already known to lie in the active used/allowed set.

This is the trace-facing selected-pivot socket: it deliberately avoids the
stronger range premise `∀ first, st.q < first → first < P → first ∈ allowed`.
-/
def taoSection7Case3_chosenActiveStepWithGap_of_selectedAllowed_oneStep
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    {st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound}
    (hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := st.q) (gapBound := gapBound)
        st.j st.s st.pre st.pres st.old)
    (hroom_next :
      ∀ first : ℕ, st.q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hallowed : hupdate.first ∈ allowed)
    (hnotLarge :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound) :
    TaoSection7Case3ChosenActiveStepWithGap
      (W := W) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (bound := bound) (n := n) (J := J)
      (xi := xi) (epsilon := epsilon) (P := P)
      (threshold := threshold) (gapBound := gapBound) st := by
  rcases
      taoSection7Case3_oneStepActiveFactsWithGap_of_selectedAllowed
        (hupdate := hupdate) (hroom_next := hroom_next)
        (hallowed := hallowed) (hnotLarge := hnotLarge) with
    ⟨hroom_first, hactive_first⟩
  exact
    { update := hupdate
      room_next := hroom_first
      active_next := hactive_first }

/--
Direct-room selected-pivot constructor for a chosen active step.

This is the same selected-update socket as
`taoSection7Case3_chosenActiveStepWithGap_of_selectedAllowed_oneStep`, but with
the successor room at the selected first-hit offset supplied directly.
-/
def taoSection7Case3_chosenActiveStepWithGap_of_selectedAllowed_oneStep_room
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    {st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound}
    (hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := st.q) (gapBound := gapBound)
        st.j st.s st.pre st.pres st.old)
    (hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold)
        P hupdate.first)
    (hallowed : hupdate.first ∈ allowed)
    (hnotLarge :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound) :
    TaoSection7Case3ChosenActiveStepWithGap
      (W := W) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (bound := bound) (n := n) (J := J)
      (xi := xi) (epsilon := epsilon) (P := P)
      (threshold := threshold) (gapBound := gapBound) st := by
  rcases
      taoSection7Case3_oneStepActiveFactsWithGap_of_selectedAllowed_room
        (hupdate := hupdate) (hroom_first := hroom_first)
        (hallowed := hallowed) (hnotLarge := hnotLarge) with
    ⟨hroom_first', hactive_first⟩
  exact
    { update := hupdate
      room_next := hroom_first'
      active_next := hactive_first }

/--
One-state selected-envelope producer for the active source trace.

It constructs the concrete one-step update from the current source state,
derives the selected first-hit membership from the full `q+1` to
later-search-bound envelope, and then applies the selected-allowed active-step
socket.  The remaining event-side obligation is the not-large-union fact for
the same allowed set.
-/
theorem taoSection7Case3_exists_chosenActiveStepWithGap_of_selectedEnvelope_activeSourceState
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    {allowed : Set ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, st.q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace allowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (hnotLarge :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          pointAt family st.old st.q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveStepWithGap
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (gapBound := gapBound) st) := by
  rcases
      taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap
        (W := W) (pointAt := pointAt) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (allowed := allowed) (P := P) (threshold := threshold)
        (q := st.q) (j := st.j) (s := st.s) (pre := st.pre)
        (pres := st.pres) (old := st.old)
        st.full hscale hlow st.room st.active hcover hroom_next hfacts
        hblock haccept with
    ⟨hupdate, hallowed⟩
  exact
    ⟨taoSection7Case3_chosenActiveStepWithGap_of_selectedAllowed_oneStep
      (st := st) (hupdate := hupdate) (hroom_next := hroom_next)
      (hallowed := hallowed) (hnotLarge := hnotLarge)⟩

/--
One-state selected-envelope producer with the not-large input supplied by the
same `E*_used` sandwich that controls the probability side.

The theorem still takes the full-envelope block trace as an input; it removes
the raw not-large-union premise from the selected-envelope active-step path.
-/
theorem taoSection7Case3_exists_chosenActiveStepWithGap_of_selectedUsed_notEStar_sandwich
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used : Set ℕ} {allowedFin : Finset ℕ} {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, st.q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace used (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          (pointAtΩ ω) family st.old st.q first →
        Γ ∈ family →
        Γ.Mem ((pointAtΩ ω) first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    ∃ hstep :
      TaoSection7Case3ChosenActiveStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (gapBound := gapBound) st,
      hstep.update.first ∈ used ∧ hstep.update.first ∈ allowedFin := by
  have hnotLarge :
      ¬ taoSection7Case3LargeTriangleUnion (pointAtΩ ω) family used bound :=
    sandwich.not_large_union_of_not_mem hω
  rcases
      taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap
        (W := W) (pointAt := pointAtΩ ω) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (allowed := used) (P := P) (threshold := threshold)
        (q := st.q) (j := st.j) (s := st.s) (pre := st.pre)
        (pres := st.pres) (old := st.old)
        st.full hscale hlow st.room st.active hcover hroom_next hfacts
        hblock haccept with
    ⟨hupdate, hused⟩
  rcases
      taoSection7Case3_oneStepActiveFactsWithGap_of_selectedAllowed
        (hupdate := hupdate) (hroom_next := hroom_next)
        (hallowed := hused) (hnotLarge := hnotLarge) with
    ⟨hroom_first, hactive_first⟩
  refine
    ⟨{ update := hupdate
       room_next := hroom_first
       active_next := hactive_first },
      hused, ?_⟩
  exact sandwich.used_mem_allowed hupdate.first hused

/--
Local-envelope variant of the selected-used sandwich bridge.

This keeps the deterministic selected-first envelope `localAllowed` separate
from the larger finite `used` set paid by the probability-side support.
-/
theorem taoSection7Case3_exists_chosenActiveStepWithGap_of_localEnvelope_notEStar_sandwich
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hlocal_subset_used : localAllowed ⊆ used)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, st.q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          (pointAtΩ ω) family st.old st.q first →
        Γ ∈ family →
        Γ.Mem ((pointAtΩ ω) first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    ∃ hstep :
      TaoSection7Case3ChosenActiveStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (gapBound := gapBound) st,
      hstep.update.first ∈ localAllowed ∧
        hstep.update.first ∈ used ∧
        hstep.update.first ∈ allowedFin := by
  have hnotLargeLocal :
      ¬ taoSection7Case3LargeTriangleUnion
        (pointAtΩ ω) family localAllowed bound :=
    sandwich.not_large_union_of_not_mem_subset hlocal_subset_used hω
  rcases
      taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap
        (W := W) (pointAt := pointAtΩ ω) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (allowed := localAllowed) (P := P) (threshold := threshold)
        (q := st.q) (j := st.j) (s := st.s) (pre := st.pre)
        (pres := st.pres) (old := st.old)
        st.full hscale hlow st.room st.active hcover hroom_next hfacts
        hblock haccept with
    ⟨hupdate, hlocal⟩
  rcases
      taoSection7Case3_oneStepActiveFactsWithGap_of_selectedAllowed
        (hupdate := hupdate) (hroom_next := hroom_next)
        (hallowed := hlocal) (hnotLarge := hnotLargeLocal) with
    ⟨hroom_first, hactive_first⟩
  have hused : hupdate.first ∈ used := hlocal_subset_used hlocal
  refine
    ⟨{ update := hupdate
       room_next := hroom_first
       active_next := hactive_first },
      hlocal, hused, ?_⟩
  exact sandwich.used_mem_allowed hupdate.first hused

/--
Direct-room local-envelope variant of the selected sandwich bridge.

The source packet still proves that the selected first hit lies in
`localAllowed`; room is requested only from that membership, not from a
universal successor-room callback.
-/
theorem taoSection7Case3_exists_chosenActiveStepWithGap_of_localEnvelope_notEStar_sandwich_room
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hlocal_subset_used : localAllowed ⊆ used)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_selected :
      ∀ first : ℕ, first ∈ localAllowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          (pointAtΩ ω) family st.old st.q first →
        Γ ∈ family →
        Γ.Mem ((pointAtΩ ω) first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    ∃ hstep :
      TaoSection7Case3ChosenActiveStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (gapBound := gapBound) st,
      hstep.update.first ∈ localAllowed ∧
        hstep.update.first ∈ used ∧
        hstep.update.first ∈ allowedFin := by
  have hnotLargeLocal :
      ¬ taoSection7Case3LargeTriangleUnion
        (pointAtΩ ω) family localAllowed bound :=
    sandwich.not_large_union_of_not_mem_subset hlocal_subset_used hω
  rcases
      taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap_room
        (W := W) (pointAt := pointAtΩ ω) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (allowed := localAllowed) (P := P) (threshold := threshold)
        (q := st.q) (j := st.j) (s := st.s) (pre := st.pre)
        (pres := st.pres) (old := st.old)
        st.full hscale hlow st.room st.active hcover hroom_selected
        hfacts hblock haccept with
    ⟨hupdate, hlocal⟩
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold)
        P hupdate.first :=
    hroom_selected hupdate.first hlocal
  rcases
      taoSection7Case3_oneStepActiveFactsWithGap_of_selectedAllowed_room
        (hupdate := hupdate) (hroom_first := hroom_first)
        (hallowed := hlocal) (hnotLarge := hnotLargeLocal) with
    ⟨hroom_first', hactive_first⟩
  have hused : hupdate.first ∈ used := hlocal_subset_used hlocal
  refine
    ⟨{ update := hupdate
       room_next := hroom_first'
       active_next := hactive_first },
      hlocal, hused, ?_⟩
  exact sandwich.used_mem_allowed hupdate.first hused

/--
Direct-room local-envelope bridge with transition-shaped acceptance.

This is the selected-envelope counterpart of the low-level
`_room_accept` packet producer.
-/
theorem taoSection7Case3_exists_chosenActiveStepWithGap_of_localEnvelope_notEStar_sandwich_room_accept
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hlocal_subset_used : localAllowed ⊆ used)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_selected :
      ∀ first : ℕ, first ∈ localAllowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept_step :
      ∀ {first : ℕ} {Γ : TaoSection7Triangle},
        first < P →
        TaoSection7Case3StoppingTransition
          (pointAtΩ ω) family st.q st.old first Γ →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        Accepts st.q st.old first Γ) :
    ∃ hstep :
      TaoSection7Case3ChosenActiveStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (gapBound := gapBound) st,
      hstep.update.first ∈ localAllowed ∧
        hstep.update.first ∈ used ∧
        hstep.update.first ∈ allowedFin := by
  have hnotLargeLocal :
      ¬ taoSection7Case3LargeTriangleUnion
        (pointAtΩ ω) family localAllowed bound :=
    sandwich.not_large_union_of_not_mem_subset hlocal_subset_used hω
  rcases
      taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap_room_accept
        (W := W) (pointAt := pointAtΩ ω) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (allowed := localAllowed) (P := P) (threshold := threshold)
        (q := st.q) (j := st.j) (s := st.s) (pre := st.pre)
        (pres := st.pres) (old := st.old)
        st.full hscale hlow st.room st.active hcover hroom_selected
        hfacts hblock haccept_step with
    ⟨hupdate, hlocal⟩
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold)
        P hupdate.first :=
    hroom_selected hupdate.first hlocal
  rcases
      taoSection7Case3_oneStepActiveFactsWithGap_of_selectedAllowed_room
        (hupdate := hupdate) (hroom_first := hroom_first)
        (hallowed := hlocal) (hnotLarge := hnotLargeLocal) with
    ⟨hroom_first', hactive_first⟩
  have hused : hupdate.first ∈ used := hlocal_subset_used hlocal
  refine
    ⟨{ update := hupdate
       room_next := hroom_first'
       active_next := hactive_first },
      hlocal, hused, ?_⟩
  exact sandwich.used_mem_allowed hupdate.first hused

/--
Direct-room local-envelope bridge with source-provenance-shaped acceptance.

This keeps the acceptance callback attached to the selected first-hit source
packet emitted by the current active source state.
-/
theorem taoSection7Case3_exists_chosenActiveStepWithGap_of_localEnvelope_notEStar_sandwich_room_acceptSource
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hlocal_subset_used : localAllowed ⊆ used)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_selected :
      ∀ first : ℕ, first ∈ localAllowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept_src :
      ∀ {candidate first : ℕ} {Γ : TaoSection7Triangle},
        TaoSection7Case3FirstHitSourceProvenance
          (taoSection7SourceBlackInDomain n xi epsilon J)
          family (pointAtΩ ω) st.j st.s st.pre st.pres P st.q st.old Γ
          candidate first →
        Accepts st.q st.old first Γ) :
    ∃ hstep :
      TaoSection7Case3ChosenActiveStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (gapBound := gapBound) st,
      hstep.update.first ∈ localAllowed ∧
        hstep.update.first ∈ used ∧
        hstep.update.first ∈ allowedFin := by
  have hnotLargeLocal :
      ¬ taoSection7Case3LargeTriangleUnion
        (pointAtΩ ω) family localAllowed bound :=
    sandwich.not_large_union_of_not_mem_subset hlocal_subset_used hω
  rcases
      taoSection7Case3_exists_oneStepRebasedSourceUpdateWithGap_and_selectedAllowed_of_fullWindowSourcePathDataWithGap_room_acceptSource
        (W := W) (pointAt := pointAtΩ ω) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (allowed := localAllowed) (P := P) (threshold := threshold)
        (q := st.q) (j := st.j) (s := st.s) (pre := st.pre)
        (pres := st.pres) (old := st.old)
        st.full hscale hlow st.room st.active hcover hroom_selected
        hfacts hblock haccept_src with
    ⟨hupdate, hlocal⟩
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold)
        P hupdate.first :=
    hroom_selected hupdate.first hlocal
  rcases
      taoSection7Case3_oneStepActiveFactsWithGap_of_selectedAllowed_room
        (hupdate := hupdate) (hroom_first := hroom_first)
        (hallowed := hlocal) (hnotLarge := hnotLargeLocal) with
    ⟨hroom_first', hactive_first⟩
  have hused : hupdate.first ∈ used := hlocal_subset_used hlocal
  refine
    ⟨{ update := hupdate
       room_next := hroom_first'
       active_next := hactive_first },
      hlocal, hused, ?_⟩
  exact sandwich.used_mem_allowed hupdate.first hused

/--
Chosen active step decorated with the selected-offset support facts that the
plain trace forgets.

The underlying `step` still drives the source-state recurrence; the extra
fields retain the probability-side membership evidence for trace-level finite
carriers.
-/
structure TaoSection7Case3ChosenActiveUsedStepWithGap
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound) :
    Type where
  step :
    TaoSection7Case3ChosenActiveStepWithGap
      (W := W) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (bound := bound) (n := n) (J := J)
      (xi := xi) (epsilon := epsilon) (P := P)
      (threshold := threshold) (gapBound := gapBound) st
  first_mem_used : step.update.first ∈ used
  first_mem_allowedFin : step.update.first ∈ allowedFin

/--
Package the selected-used sandwich bridge as a support-decorated chosen step.
-/
theorem taoSection7Case3_exists_chosenActiveUsedStepWithGap_of_selectedUsed_notEStar_sandwich
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used : Set ℕ} {allowedFin : Finset ℕ} {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, st.q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace used (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          (pointAtΩ ω) family st.old st.q first →
        Γ ∈ family →
        Γ.Mem ((pointAtΩ ω) first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st) := by
  rcases
      taoSection7Case3_exists_chosenActiveStepWithGap_of_selectedUsed_notEStar_sandwich
        (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
        (Accepts := Accepts) (EStarUsed := EStarUsed) (used := used)
        (allowedFin := allowedFin) (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (gapBound := gapBound) st sandwich hω
        hscale hlow hcover hroom_next hfacts hblock haccept with
    ⟨hstep, hused, hallowedFin⟩
  exact
    ⟨{ step := hstep
       first_mem_used := hused
       first_mem_allowedFin := hallowedFin }⟩

/--
Package the local-envelope sandwich bridge as a support-decorated chosen step.
-/
theorem taoSection7Case3_exists_chosenActiveUsedStepWithGap_of_localEnvelope_notEStar_sandwich
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hlocal_subset_used : localAllowed ⊆ used)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, st.q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          (pointAtΩ ω) family st.old st.q first →
        Γ ∈ family →
        Γ.Mem ((pointAtΩ ω) first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st) := by
  rcases
      taoSection7Case3_exists_chosenActiveStepWithGap_of_localEnvelope_notEStar_sandwich
        (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
        (Accepts := Accepts) (EStarUsed := EStarUsed) (used := used)
        (localAllowed := localAllowed) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st sandwich hω hlocal_subset_used hscale
        hlow hcover hroom_next hfacts hblock haccept with
    ⟨hstep, _hlocal, hused, hallowedFin⟩
  exact
    ⟨{ step := hstep
       first_mem_used := hused
       first_mem_allowedFin := hallowedFin }⟩

/--
Chosen active step retaining both the local envelope membership used for the
one-state construction and the larger probability-side used/finite support.
-/
structure TaoSection7Case3ChosenActiveLocalUsedStepWithGap
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {localAllowed used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound) :
    Type where
  usedStep :
    TaoSection7Case3ChosenActiveUsedStepWithGap
      (W := W) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
      (bound := bound) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := gapBound) st
  first_mem_local : usedStep.step.update.first ∈ localAllowed

/--
Package the local-envelope sandwich bridge while retaining the local-envelope
membership needed for bounded recursion.
-/
theorem taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_localEnvelope_notEStar_sandwich
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hlocal_subset_used : localAllowed ⊆ used)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, st.q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          (pointAtΩ ω) family st.old st.q first →
        Γ ∈ family →
        Γ.Mem ((pointAtΩ ω) first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (localAllowed := localAllowed)
        (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st) := by
  rcases
      taoSection7Case3_exists_chosenActiveStepWithGap_of_localEnvelope_notEStar_sandwich
        (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
        (Accepts := Accepts) (EStarUsed := EStarUsed) (used := used)
        (localAllowed := localAllowed) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st sandwich hω hlocal_subset_used hscale
        hlow hcover hroom_next hfacts hblock haccept with
    ⟨hstep, hlocal, hused, hallowedFin⟩
  exact
    ⟨{ usedStep :=
          { step := hstep
            first_mem_used := hused
            first_mem_allowedFin := hallowedFin }
       first_mem_local := hlocal }⟩

/--
Direct-room version of the local-used sandwich package.

This retains the local-envelope membership while using only selected-offset
room, preparing the finite bounded trace for a separate room-depth hypothesis.
-/
theorem taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_localEnvelope_notEStar_sandwich_room
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hlocal_subset_used : localAllowed ⊆ used)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_selected :
      ∀ first : ℕ, first ∈ localAllowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          (pointAtΩ ω) family st.old st.q first →
        Γ ∈ family →
        Γ.Mem ((pointAtΩ ω) first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (localAllowed := localAllowed)
        (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st) := by
  rcases
      taoSection7Case3_exists_chosenActiveStepWithGap_of_localEnvelope_notEStar_sandwich_room
        (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
        (Accepts := Accepts) (EStarUsed := EStarUsed) (used := used)
        (localAllowed := localAllowed) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st sandwich hω hlocal_subset_used hscale
        hlow hcover hroom_selected hfacts hblock haccept with
    ⟨hstep, hlocal, hused, hallowedFin⟩
  exact
    ⟨{ usedStep :=
          { step := hstep
            first_mem_used := hused
            first_mem_allowedFin := hallowedFin }
       first_mem_local := hlocal }⟩

/--
Direct-room local-used package with transition-shaped acceptance.
-/
theorem taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_localEnvelope_notEStar_sandwich_room_accept
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hlocal_subset_used : localAllowed ⊆ used)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_selected :
      ∀ first : ℕ, first ∈ localAllowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept_step :
      ∀ {first : ℕ} {Γ : TaoSection7Triangle},
        first < P →
        TaoSection7Case3StoppingTransition
          (pointAtΩ ω) family st.q st.old first Γ →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (localAllowed := localAllowed)
        (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st) := by
  rcases
      taoSection7Case3_exists_chosenActiveStepWithGap_of_localEnvelope_notEStar_sandwich_room_accept
        (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
        (Accepts := Accepts) (EStarUsed := EStarUsed) (used := used)
        (localAllowed := localAllowed) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st sandwich hω hlocal_subset_used hscale
        hlow hcover hroom_selected hfacts hblock haccept_step with
    ⟨hstep, hlocal, hused, hallowedFin⟩
  exact
    ⟨{ usedStep :=
          { step := hstep
            first_mem_used := hused
            first_mem_allowedFin := hallowedFin }
       first_mem_local := hlocal }⟩

/--
Direct-room local-used package with source-provenance-shaped acceptance.
-/
theorem taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_localEnvelope_notEStar_sandwich_room_acceptSource
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold gapBound)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed used allowedFin bound)
    (hω : ω ∉ EStarUsed)
    (hlocal_subset_used : localAllowed ⊆ used)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_selected :
      ∀ first : ℕ, first ∈ localAllowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold st.q -
          (st.q + 1)))
    (haccept_src :
      ∀ {candidate first : ℕ} {Γ : TaoSection7Triangle},
        TaoSection7Case3FirstHitSourceProvenance
          (taoSection7SourceBlackInDomain n xi epsilon J)
          family (pointAtΩ ω) st.j st.s st.pre st.pres P st.q st.old Γ
          candidate first →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (localAllowed := localAllowed)
        (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st) := by
  rcases
      taoSection7Case3_exists_chosenActiveStepWithGap_of_localEnvelope_notEStar_sandwich_room_acceptSource
        (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
        (Accepts := Accepts) (EStarUsed := EStarUsed) (used := used)
        (localAllowed := localAllowed) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st sandwich hω hlocal_subset_used hscale
        hlow hcover hroom_selected hfacts hblock haccept_src with
    ⟨hstep, hlocal, hused, hallowedFin⟩
  exact
    ⟨{ usedStep :=
          { step := hstep
            first_mem_used := hused
            first_mem_allowedFin := hallowedFin }
       first_mem_local := hlocal }⟩

/--
Pre-trace base-Kcut range instantiation of the local-used one-step bridge.

At recursive step `i`, the current iterate bound places the local selected
envelope inside the fixed carrier chosen before the trace is built.  This keeps
the `E*_used` support noncircular while producing the local-used step data
needed by `seqLocalUsed`.
-/
theorem taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_baseKcutRange_notEStar_sandwich
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut R start i : ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
            start + 1))
        bound)
    (hω : ω ∉ EStarUsed)
    (htrace_le :
      st.q ≤ ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i]) start)
    (hi : i + 1 ≤ R)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, st.q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound
            (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold)
          P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          (pointAtΩ ω) family st.old st.q first →
        Γ ∈ family →
        Γ.Mem ((pointAtΩ ω) first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts)
        (localAllowed :=
          taoSection7Case3LocalSelectedEnvelope
            (taoSection7Case3ExitGapBoundWithBase base Kcut)
            threshold st.q)
        (used :=
          {p : ℕ |
            p ∈ Finset.range
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
                start + 1)})
        (allowedFin :=
          Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
              start + 1))
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st) := by
  let allowedFin : Finset ℕ :=
    Finset.range
      (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
        start + 1)
  let used : Set ℕ := {p : ℕ | p ∈ allowedFin}
  let localAllowed : Set ℕ :=
    taoSection7Case3LocalSelectedEnvelope
      (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold st.q
  have hlocal_subset_used : localAllowed ⊆ used := by
    intro p hp
    exact
      taoSection7Case3_localSelectedEnvelope_subset_baseKcutIterateRange
        (base := base) (Kcut := Kcut) (threshold := threshold)
        (R := R) (start := start) (q := st.q) (i := i)
        htrace_le hi (by simpa [localAllowed] using hp)
  have hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBoundWithBase base Kcut)
          threshold st.q - (st.q + 1)) := by
    simpa [localAllowed] using
      (TaoSection7Case3AllowedBlockTrace.localSelectedEnvelope
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
        (threshold := threshold) (q := st.q))
  change
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (localAllowed := localAllowed)
        (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st)
  exact
    taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_localEnvelope_notEStar_sandwich
      (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
      (Accepts := Accepts) (EStarUsed := EStarUsed)
      (used := used) (localAllowed := localAllowed)
      (allowedFin := allowedFin) (bound := bound) (n := n) (J := J)
      (xi := xi) (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
      st sandwich hω hlocal_subset_used hscale hlow hcover hroom_next
      hfacts hblock haccept

/--
Room-depth split version of the base-Kcut local-used one-step bridge.

The trace/support carrier uses `Rtrace`, while deterministic successor room is
proved from the independent room depth `Rroom`.  The hypothesis
`Rtrace + 1 ≤ Rroom` is the explicit last-step margin needed because selected
room consumes two base-Kcut steps from the current state.
-/
theorem taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_baseKcutRange_notEStar_sandwich_roomDepth
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace Rroom start i : ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
        bound)
    (hω : ω ∉ EStarUsed)
    (htrace_le :
      st.q ≤ ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i]) start)
    (hi : i < Rtrace)
    (hroom_iter :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold Rroom start P)
    (hroom_depth : Rtrace + 1 ≤ Rroom)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        TaoSection7Case3FirstAfterTriangleHitFrom
          (pointAtΩ ω) family st.old st.q first →
        Γ ∈ family →
        Γ.Mem ((pointAtΩ ω) first) →
        Γ ≠ st.old →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts)
        (localAllowed :=
          taoSection7Case3LocalSelectedEnvelope
            (taoSection7Case3ExitGapBoundWithBase base Kcut)
            threshold st.q)
        (used :=
          {p : ℕ |
            p ∈ Finset.range
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
                start + 1)})
        (allowedFin :=
          Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1))
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st) := by
  let allowedFin : Finset ℕ :=
    Finset.range
      (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
        start + 1)
  let used : Set ℕ := {p : ℕ | p ∈ allowedFin}
  let localAllowed : Set ℕ :=
    taoSection7Case3LocalSelectedEnvelope
      (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold st.q
  have hlocal_subset_used : localAllowed ⊆ used := by
    intro p hp
    exact
      taoSection7Case3_localSelectedEnvelope_subset_baseKcutIterateRange
        (base := base) (Kcut := Kcut) (threshold := threshold)
        (R := Rtrace) (start := start) (q := st.q) (i := i)
        htrace_le (Nat.succ_le_of_lt hi) (by simpa [localAllowed] using hp)
  have hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBoundWithBase base Kcut)
          threshold st.q - (st.q + 1)) := by
    simpa [localAllowed] using
      (TaoSection7Case3AllowedBlockTrace.localSelectedEnvelope
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
        (threshold := threshold) (q := st.q))
  have hroom_selected :
      ∀ first : ℕ, first ∈ localAllowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound
            (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold)
          P first := by
    intro first hfirst
    have hi_room : i + 2 ≤ Rroom := by
      have hi_trace : i + 2 ≤ Rtrace + 1 := by omega
      exact hi_trace.trans hroom_depth
    exact
      taoSection7Case3_exitRoom_of_baseKcutIterateRoom_of_mem_localSelectedEnvelope
        (base := base) (Kcut := Kcut) (threshold := threshold)
        (R := Rroom) (start := start) (P := P) (q := st.q)
        (i := i) (p := first) hroom_iter htrace_le hi_room
        (by simpa [localAllowed] using hfirst)
  change
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (localAllowed := localAllowed)
        (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st)
  exact
    taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_localEnvelope_notEStar_sandwich_room
      (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
      (Accepts := Accepts) (EStarUsed := EStarUsed)
      (used := used) (localAllowed := localAllowed)
      (allowedFin := allowedFin) (bound := bound) (n := n) (J := J)
      (xi := xi) (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
      st sandwich hω hlocal_subset_used hscale hlow hcover hroom_selected
      hfacts hblock haccept

/--
Room-depth split base-Kcut step with transition-shaped acceptance.

This keeps the room-depth count convention from `_roomDepth` while replacing
the broad acceptance callback by a premise on the selected stopping transition.
-/
theorem taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_baseKcutRange_notEStar_sandwich_roomDepth_accept
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace Rroom start i : ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
        bound)
    (hω : ω ∉ EStarUsed)
    (htrace_le :
      st.q ≤ ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i]) start)
    (hi : i < Rtrace)
    (hroom_iter :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold Rroom start P)
    (hroom_depth : Rtrace + 1 ≤ Rroom)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (haccept_step :
      ∀ {first : ℕ} {Γ : TaoSection7Triangle},
        first < P →
        TaoSection7Case3StoppingTransition
          (pointAtΩ ω) family st.q st.old first Γ →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts)
        (localAllowed :=
          taoSection7Case3LocalSelectedEnvelope
            (taoSection7Case3ExitGapBoundWithBase base Kcut)
            threshold st.q)
        (used :=
          {p : ℕ |
            p ∈ Finset.range
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
                start + 1)})
        (allowedFin :=
          Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1))
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st) := by
  let allowedFin : Finset ℕ :=
    Finset.range
      (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
        start + 1)
  let used : Set ℕ := {p : ℕ | p ∈ allowedFin}
  let localAllowed : Set ℕ :=
    taoSection7Case3LocalSelectedEnvelope
      (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold st.q
  have hlocal_subset_used : localAllowed ⊆ used := by
    intro p hp
    exact
      taoSection7Case3_localSelectedEnvelope_subset_baseKcutIterateRange
        (base := base) (Kcut := Kcut) (threshold := threshold)
        (R := Rtrace) (start := start) (q := st.q) (i := i)
        htrace_le (Nat.succ_le_of_lt hi) (by simpa [localAllowed] using hp)
  have hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBoundWithBase base Kcut)
          threshold st.q - (st.q + 1)) := by
    simpa [localAllowed] using
      (TaoSection7Case3AllowedBlockTrace.localSelectedEnvelope
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
        (threshold := threshold) (q := st.q))
  have hroom_selected :
      ∀ first : ℕ, first ∈ localAllowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound
            (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold)
          P first := by
    intro first hfirst
    have hi_room : i + 2 ≤ Rroom := by
      have hi_trace : i + 2 ≤ Rtrace + 1 := by omega
      exact hi_trace.trans hroom_depth
    exact
      taoSection7Case3_exitRoom_of_baseKcutIterateRoom_of_mem_localSelectedEnvelope
        (base := base) (Kcut := Kcut) (threshold := threshold)
        (R := Rroom) (start := start) (P := P) (q := st.q)
        (i := i) (p := first) hroom_iter htrace_le hi_room
        (by simpa [localAllowed] using hfirst)
  change
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (localAllowed := localAllowed)
        (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st)
  exact
    taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_localEnvelope_notEStar_sandwich_room_accept
      (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
      (Accepts := Accepts) (EStarUsed := EStarUsed)
      (used := used) (localAllowed := localAllowed)
      (allowedFin := allowedFin) (bound := bound) (n := n) (J := J)
      (xi := xi) (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
      st sandwich hω hlocal_subset_used hscale hlow hcover hroom_selected
      hfacts hblock haccept_step

/--
Room-depth split base-Kcut step with source-provenance-shaped acceptance.

The acceptance callback is applied to the selected first-hit source packet for
the current trace state.
-/
theorem taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_baseKcutRange_notEStar_sandwich_roomDepth_acceptSource
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace Rroom start i : ℕ}
    (st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
        bound)
    (hω : ω ∉ EStarUsed)
    (htrace_le :
      st.q ≤ ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i]) start)
    (hi : i < Rtrace)
    (hroom_iter :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold Rroom start P)
    (hroom_depth : Rtrace + 1 ≤ Rroom)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (haccept_src :
      ∀ {candidate first : ℕ} {Γ : TaoSection7Triangle},
        TaoSection7Case3FirstHitSourceProvenance
          (taoSection7SourceBlackInDomain n xi epsilon J)
          family (pointAtΩ ω) st.j st.s st.pre st.pres P st.q st.old Γ
          candidate first →
        Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts)
        (localAllowed :=
          taoSection7Case3LocalSelectedEnvelope
            (taoSection7Case3ExitGapBoundWithBase base Kcut)
            threshold st.q)
        (used :=
          {p : ℕ |
            p ∈ Finset.range
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
                start + 1)})
        (allowedFin :=
          Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1))
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st) := by
  let allowedFin : Finset ℕ :=
    Finset.range
      (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
        start + 1)
  let used : Set ℕ := {p : ℕ | p ∈ allowedFin}
  let localAllowed : Set ℕ :=
    taoSection7Case3LocalSelectedEnvelope
      (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold st.q
  have hlocal_subset_used : localAllowed ⊆ used := by
    intro p hp
    exact
      taoSection7Case3_localSelectedEnvelope_subset_baseKcutIterateRange
        (base := base) (Kcut := Kcut) (threshold := threshold)
        (R := Rtrace) (start := start) (q := st.q) (i := i)
        htrace_le (Nat.succ_le_of_lt hi) (by simpa [localAllowed] using hp)
  have hblock :
      TaoSection7Case3AllowedBlockTrace localAllowed (st.q + 1)
        (taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBoundWithBase base Kcut)
          threshold st.q - (st.q + 1)) := by
    simpa [localAllowed] using
      (TaoSection7Case3AllowedBlockTrace.localSelectedEnvelope
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
        (threshold := threshold) (q := st.q))
  have hroom_selected :
      ∀ first : ℕ, first ∈ localAllowed →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound
            (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold)
          P first := by
    intro first hfirst
    have hi_room : i + 2 ≤ Rroom := by
      have hi_trace : i + 2 ≤ Rtrace + 1 := by omega
      exact hi_trace.trans hroom_depth
    exact
      taoSection7Case3_exitRoom_of_baseKcutIterateRoom_of_mem_localSelectedEnvelope
        (base := base) (Kcut := Kcut) (threshold := threshold)
        (R := Rroom) (start := start) (P := P) (q := st.q)
        (i := i) (p := first) hroom_iter htrace_le hi_room
        (by simpa [localAllowed] using hfirst)
  change
    Nonempty
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts) (localAllowed := localAllowed)
        (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st)
  exact
    taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_localEnvelope_notEStar_sandwich_room_acceptSource
      (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
      (Accepts := Accepts) (EStarUsed := EStarUsed)
      (used := used) (localAllowed := localAllowed)
      (allowedFin := allowedFin) (bound := bound) (n := n) (J := J)
      (xi := xi) (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
      st sandwich hω hlocal_subset_used hscale hlow hcover hroom_selected
      hfacts hblock haccept_src

namespace TaoSection7Case3ChosenActiveLocalUsedStepWithGap

theorem first_le_baseKcutNextBound
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut : ℕ}
    {st :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hstep :
      TaoSection7Case3ChosenActiveLocalUsedStepWithGap
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts)
        (localAllowed :=
          taoSection7Case3LocalSelectedEnvelope
            (taoSection7Case3ExitGapBoundWithBase base Kcut)
            threshold st.q)
        (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st) :
    hstep.usedStep.step.update.first ≤
      taoSection7Case3BaseKcutNextBound base Kcut threshold st.q :=
  taoSection7Case3_le_baseKcutNextBound_of_mem_localSelectedEnvelope
    hstep.first_mem_local

end TaoSection7Case3ChosenActiveLocalUsedStepWithGap

/--
Finite on-trace local-used driver for the bounded Case 3 recurrence.

Unlike `seqLocalUsed`, this object does not require a global advance oracle for
arbitrary active states.  Its steps are only required on the states already
constructed, together with the propagated base-Kcut iterate bound.
-/
structure TaoSection7Case3BoundedLocalUsedTrace
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut R start : ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)) :
    Type where
  state :
    ℕ →
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)
  state_zero : state 0 = st0
  transition :
    ∀ i : ℕ, (hi : i < R) →
      { step :
        TaoSection7Case3ChosenActiveLocalUsedStepWithGap
          (W := W) (family := family) (pointAt := pointAt)
          (Accepts := Accepts)
          (localAllowed :=
            taoSection7Case3LocalSelectedEnvelope
              (taoSection7Case3ExitGapBoundWithBase base Kcut)
              threshold (state i).q)
          (used := used) (allowedFin := allowedFin)
          (bound := bound) (n := n) (J := J) (xi := xi)
          (epsilon := epsilon) (P := P) (threshold := threshold)
          (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
          (state i) //
        state (i + 1) =
          TaoSection7Case3ChosenActiveStepWithGap.nextState
            (step.usedStep.step) }
  q_bound :
    ∀ i : ℕ, (hi : i ≤ R) →
      (state i).q ≤
        ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i]) start

namespace TaoSection7Case3BoundedLocalUsedTrace

/--
The bounded local-used trace's explicit first-`Rtail + 1` stopping prefix.

This is a prefix object only.  It is not the full terminal source stopping run
unless separate terminal/no-later-black evidence extends it to Tao's maximal
run.
-/
def prefixSteps
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    List (ℕ × TaoSection7Triangle) :=
  ((htrace.state 0).q, (htrace.state 0).old) ::
    taoSection7Case3IndexedEncounterTail
      (fun k => (htrace.state k).q)
      (fun k => (htrace.state k).old) 0 Rtail

theorem prefixSteps_length
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    htrace.prefixSteps.length = Rtail + 1 := by
  simp [prefixSteps, taoSection7Case3IndexedEncounterTail_length]

theorem prefixSteps_hasAtLeast
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    TaoSection7Case3SourceStoppingRun.HasAtLeast
      htrace.prefixSteps (Rtail + 1) := by
  simpa [prefixSteps] using
    taoSection7Case3_hasAtLeast_cons_indexedTail
      (fun k => (htrace.state k).q)
      (fun k => (htrace.state k).old) 0 Rtail

theorem prefixSteps_tR?
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    TaoSection7Case3SourceStoppingRun.tR?
        htrace.prefixSteps (Rtail + 1) =
      some ((htrace.state Rtail).q) := by
  simpa [prefixSteps] using
    taoSection7Case3_tR?_cons_indexedTail_last
      (fun k => (htrace.state k).q)
      (fun k => (htrace.state k).old) 0 Rtail

theorem prefixSteps_last?
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    TaoSection7Case3StoppingLast? htrace.prefixSteps =
      some ((htrace.state Rtail).q, (htrace.state Rtail).old) := by
  simpa [prefixSteps] using
    taoSection7Case3StoppingLast?_cons_indexedTail
      (fun k => (htrace.state k).q)
      (fun k => (htrace.state k).old) 0 Rtail

theorem prefixSteps_length_and_tR?
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    htrace.prefixSteps.length = Rtail + 1 ∧
      TaoSection7Case3SourceStoppingRun.tR?
          htrace.prefixSteps (Rtail + 1) =
        some ((htrace.state Rtail).q) :=
  ⟨htrace.prefixSteps_length, htrace.prefixSteps_tR?⟩

theorem q_ltP
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) :
    ∀ i : ℕ, i ≤ Rtrace → (htrace.state i).q < P := by
  intro i hi
  cases i with
  | zero =>
      simpa [htrace.state_zero] using hfirst0_ltP
  | succ k =>
      have hk : k < Rtrace := Nat.succ_le_iff.mp hi
      let htrans := htrace.transition k hk
      let hstep := htrans.1.usedStep.step
      have hq :
          (htrace.state (k + 1)).q = hstep.update.first := by
        simpa [hstep, TaoSection7Case3ChosenActiveStepWithGap.nextState] using
          congrArg (fun st => st.q) htrans.2
      simpa [hq] using hstep.update.first_ltP

theorem endpoint_q_ltP
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) :
    (htrace.state Rtrace).q < P :=
  htrace.q_ltP hfirst0_ltP Rtrace (Nat.le_refl Rtrace)

end TaoSection7Case3BoundedLocalUsedTrace

/--
Project one bounded local-used trace transition to the indexed rebased-update
packet consumed by the finite `PrefixRInputs` layer.
-/
def taoSection7Case3_indexedRebasedSourceUpdateWithGap_of_boundedLocalUsedTrace_step
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0)
    (i : ℕ) (hi : i < Rtail) :
    TaoSection7Case3IndexedRebasedSourceUpdateWithGap
      (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
      (family := family) (pointAt := pointAt) (Accepts := Accepts)
      (n := n) (J := J) (xi := xi) (epsilon := epsilon)
      (P := P) (threshold := threshold)
      (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
      (fun k => (htrace.state k).q)
      (fun k => (htrace.state k).old)
      (fun k => (htrace.state k).j)
      (fun k => (htrace.state k).s)
      (fun k => (htrace.state k).pre)
      (fun k => (htrace.state k).pres) i := by
  let htrans := htrace.transition i hi
  let hstep := htrans.1.usedStep.step
  exact
    TaoSection7Case3OneStepRebasedSourceUpdateWithGap.to_indexedRebasedSourceUpdateWithGap
      (hupdate := hstep.update)
      (by
        simpa [hstep, TaoSection7Case3ChosenActiveStepWithGap.nextState] using
          congrArg (fun st => st.q) htrans.2)
      (by
        simpa [hstep, TaoSection7Case3ChosenActiveStepWithGap.nextState] using
          congrArg (fun st => st.old) htrans.2)
      (by
        simpa [hstep, TaoSection7Case3ChosenActiveStepWithGap.nextState] using
          congrArg (fun st => st.j) htrans.2)
      (by
        simpa [hstep, TaoSection7Case3ChosenActiveStepWithGap.nextState] using
          congrArg (fun st => st.s) htrans.2)
      (by
        simpa [hstep, TaoSection7Case3ChosenActiveStepWithGap.nextState] using
          congrArg (fun st => st.pre) htrans.2)
      (by
        simpa [hstep, TaoSection7Case3ChosenActiveStepWithGap.nextState] using
          congrArg (fun st => st.pres) htrans.2)

/--
Bounded local-used traces feed the existing indexed rebased-update consumer.

The trace contributes the state arrays and per-step update packets.  The
initial stopping step and initial finite-window proof remain explicit inputs,
because a bounded active trace by itself does not identify the source run's
chosen starting stop.
-/
theorem taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_boundedLocalUsedTrace
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    TaoSection7Case3PrefixRInputs
        (taoSection7SourceBlackInDomain n xi epsilon J)
        family pointAt Accepts P (Rtail + 1)
        ((htrace.state 0).q) ((htrace.state 0).old)
        (taoSection7Case3IndexedEncounterTail
          (fun k => (htrace.state k).q)
          (fun k => (htrace.state k).old) 0 Rtail) ∧
      ∀ i : ℕ, i ≤ Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold ((htrace.state i).q)
          (taoSection7Case3ExitGapBoundWithBase base Kcut)
          ((htrace.state i).j) ((htrace.state i).s)
          ((htrace.state i).pre) ((htrace.state i).pres) := by
  have hinit0 :
      TaoSection7Case3InitialStoppingStep pointAt family
        ((htrace.state 0).q) ((htrace.state 0).old) := by
    simpa [htrace.state_zero] using hinit
  have hfirst0 :
      (htrace.state 0).q < P := by
    simpa [htrace.state_zero] using hfirst0_ltP
  exact
    taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_indexedSourceStateUpdates
      (black := taoSection7SourceBlackInDomain n xi epsilon J)
      (family := family) (pointAt := pointAt) (Accepts := Accepts)
      (n := n) (J := J) (xi := xi) (epsilon := epsilon)
      (P := P) (threshold := threshold)
      (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
      (fun k => (htrace.state k).q)
      (fun k => (htrace.state k).old)
      (fun k => (htrace.state k).j)
      (fun k => (htrace.state k).s)
      (fun k => (htrace.state k).pre)
      (fun k => (htrace.state k).pres)
      hinit0 hfirst0 (htrace.state 0).full
      (by
        intro i hi
        exact
          taoSection7Case3_indexedRebasedSourceUpdateWithGap_of_boundedLocalUsedTrace_step
            (htrace := htrace) i hi |>.to_sourceStateUpdate)

namespace TaoSection7Case3ActualRunSourceIdentity

/--
Endpoint-window extractor for an actual run whose first stops are identified
with a bounded local-used trace.

This is still only a take-prefix adapter: the equality identifying
`steps.take (Rtail + 1)` with the constructed trace prefix is an explicit
premise.
-/
theorem tR_ltP_of_boundedLocalUsedTrace_take_eq
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start tR lemma79Count : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family n J xi epsilon P steps (Rtail + 1) tR
        lemma79Count)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0)
    (htake :
      steps.take (Rtail + 1) =
        ((htrace.state 0).q, (htrace.state 0).old) ::
          taoSection7Case3IndexedEncounterTail
            (fun k => (htrace.state k).q)
            (fun k => (htrace.state k).old) 0 Rtail) :
    tR < P :=
  h.tR_ltP_of_prefixRInputs_take_eq htake
    (taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_boundedLocalUsedTrace
      (hinit := hinit) (hfirst0_ltP := hfirst0_ltP)
      (htrace := htrace)).1

end TaoSection7Case3ActualRunSourceIdentity

namespace TaoSection7Case3StoppingTail

/--
Compare an actual stopping tail with the tail carried by a bounded local-used
trace.

The equalities `hq` and `hold` are the predecessor transport needed at each
induction step: after comparing one pair, the recursive call uses that pair
equality to align the next actual predecessor with the next bounded-trace
state.
-/
theorem take_eq_indexedEncounterTail_of_boundedLocalUsedTrace
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace start : ℕ}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0)
    {q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (htail : TaoSection7Case3StoppingTail pointAt family q old steps) :
    ∀ (i Rtail : ℕ),
      i + Rtail ≤ Rtrace →
        q = (htrace.state i).q →
          old = (htrace.state i).old →
            Rtail ≤ steps.length →
              steps.take Rtail =
                taoSection7Case3IndexedEncounterTail
                  (fun k => (htrace.state k).q)
                  (fun k => (htrace.state k).old) i Rtail := by
  intro i Rtail
  induction Rtail generalizing i q old steps with
  | zero =>
      intro _htrace_room _hq _hold _hlen
      simp [taoSection7Case3IndexedEncounterTail]
  | succ Rtail ih =>
      intro htrace_room hq hold hlen
      cases steps with
      | nil =>
          simp at hlen
      | cons head rest =>
          cases head with
          | mk first Γ =>
              have hstep :
                  TaoSection7Case3StoppingTransition
                    pointAt family q old first Γ :=
                TaoSection7Case3StoppingTail.head_step htail
              have htail_rest :
                  TaoSection7Case3StoppingTail
                    pointAt family first Γ rest :=
                TaoSection7Case3StoppingTail.tail htail
              have hi : i < Rtrace := by omega
              let htrans := htrace.transition i hi
              let hchosen := htrans.1.usedStep.step
              let hupdate := hchosen.update
              subst q
              subst old
              have hactual_eq_update :
                  (first, Γ) = (hupdate.first, hupdate.triangle) :=
                hupdate.pair_eq_of_pairwiseDisjoint_stoppingTransition
                  hpair hstep
              have hupdate_eq_next :
                  (hupdate.first, hupdate.triangle) =
                    ((htrace.state (i + 1)).q,
                      (htrace.state (i + 1)).old) := by
                apply Prod.ext
                · simpa [hchosen, hupdate,
                    TaoSection7Case3ChosenActiveStepWithGap.nextState] using
                    (congrArg (fun st => st.q) htrans.2).symm
                · simpa [hchosen, hupdate,
                    TaoSection7Case3ChosenActiveStepWithGap.nextState] using
                    (congrArg (fun st => st.old) htrans.2).symm
              have hactual_eq_next :
                  (first, Γ) =
                    ((htrace.state (i + 1)).q,
                      (htrace.state (i + 1)).old) :=
                hactual_eq_update.trans hupdate_eq_next
              have hlen_tail : Rtail ≤ rest.length := by
                simpa using Nat.succ_le_succ_iff.mp hlen
              have hrec :
                  rest.take Rtail =
                    taoSection7Case3IndexedEncounterTail
                      (fun k => (htrace.state k).q)
                      (fun k => (htrace.state k).old) (i + 1) Rtail :=
                ih htail_rest (i + 1)
                  (by omega)
                  (congrArg Prod.fst hactual_eq_next)
                  (congrArg Prod.snd hactual_eq_next)
                  hlen_tail
              simp [taoSection7Case3IndexedEncounterTail, hactual_eq_next,
                hrec]

end TaoSection7Case3StoppingTail

namespace TaoSection7Case3StoppingPrefix

/--
The first `Rtail + 1` stops of an actual stopping prefix agree with a bounded
local-used trace when the initial pair agrees.

The proof uses the initial pairwise-disjoint comparison for the head and
`TaoSection7Case3StoppingTail.take_eq_indexedEncounterTail_of_boundedLocalUsedTrace`
for the predecessor-transport tail induction.
-/
theorem take_eq_boundedLocalUsedTrace_prefix
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (hlen : Rtail + 1 ≤ steps.length)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    steps.take (Rtail + 1) =
      ((htrace.state 0).q, (htrace.state 0).old) ::
        taoSection7Case3IndexedEncounterTail
          (fun k => (htrace.state k).q)
          (fun k => (htrace.state k).old) 0 Rtail := by
  cases steps with
  | nil =>
      simp at hlen
  | cons head rest =>
      cases head with
      | mk first Γ =>
          have hinit_actual :
              TaoSection7Case3InitialStoppingStep
                pointAt family first Γ :=
            TaoSection7Case3StoppingPrefix.head_initial hprefix
          have htail_actual :
              TaoSection7Case3StoppingTail pointAt family first Γ rest :=
            TaoSection7Case3StoppingPrefix.tail hprefix
          have hinit_trace :
              TaoSection7Case3InitialStoppingStep
                pointAt family ((htrace.state 0).q)
                  ((htrace.state 0).old) := by
            simpa [htrace.state_zero] using hinit
          have hhead_eq :
              (first, Γ) =
                ((htrace.state 0).q, (htrace.state 0).old) :=
            hinit_actual.pair_eq_of_pairwiseDisjoint hpair hinit_trace
          have hlen_tail : Rtail ≤ rest.length := by
            simpa using Nat.succ_le_succ_iff.mp hlen
          have htail_eq :
              rest.take Rtail =
                taoSection7Case3IndexedEncounterTail
                  (fun k => (htrace.state k).q)
                  (fun k => (htrace.state k).old) 0 Rtail :=
            TaoSection7Case3StoppingTail.take_eq_indexedEncounterTail_of_boundedLocalUsedTrace
              (hpair := hpair) (htrace := htrace) htail_actual 0 Rtail
              (by omega)
              (congrArg Prod.fst hhead_eq)
              (congrArg Prod.snd hhead_eq)
              hlen_tail
          simp [hhead_eq, htail_eq]

theorem take_eq_boundedLocalUsedTrace_prefix_of_le
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace Rtail start : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hprefix : TaoSection7Case3StoppingPrefix pointAt family steps)
    (htrace_len : Rtail ≤ Rtrace)
    (hlen : Rtail + 1 ≤ steps.length)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) :
    steps.take (Rtail + 1) =
      ((htrace.state 0).q, (htrace.state 0).old) ::
        taoSection7Case3IndexedEncounterTail
          (fun k => (htrace.state k).q)
          (fun k => (htrace.state k).old) 0 Rtail := by
  cases steps with
  | nil =>
      simp at hlen
  | cons head rest =>
      cases head with
      | mk first Γ =>
          have hinit_actual :
              TaoSection7Case3InitialStoppingStep
                pointAt family first Γ :=
            TaoSection7Case3StoppingPrefix.head_initial hprefix
          have htail_actual :
              TaoSection7Case3StoppingTail pointAt family first Γ rest :=
            TaoSection7Case3StoppingPrefix.tail hprefix
          have hinit_trace :
              TaoSection7Case3InitialStoppingStep
                pointAt family ((htrace.state 0).q)
                  ((htrace.state 0).old) := by
            simpa [htrace.state_zero] using hinit
          have hhead_eq :
              (first, Γ) =
                ((htrace.state 0).q, (htrace.state 0).old) :=
            hinit_actual.pair_eq_of_pairwiseDisjoint hpair hinit_trace
          have hlen_tail : Rtail ≤ rest.length := by
            simpa using Nat.succ_le_succ_iff.mp hlen
          have htail_eq :
              rest.take Rtail =
                taoSection7Case3IndexedEncounterTail
                  (fun k => (htrace.state k).q)
                  (fun k => (htrace.state k).old) 0 Rtail :=
            TaoSection7Case3StoppingTail.take_eq_indexedEncounterTail_of_boundedLocalUsedTrace
              (hpair := hpair) (htrace := htrace) htail_actual 0 Rtail
              (by simpa using htrace_len)
              (congrArg Prod.fst hhead_eq)
              (congrArg Prod.snd hhead_eq)
              hlen_tail
          simp [hhead_eq, htail_eq]

end TaoSection7Case3StoppingPrefix

namespace TaoSection7Case3SourceStoppingRun

/--
A complete source stopping run cannot terminate before the bounded local-used
trace length.

If the run were empty, its terminal no-initial-hit certificate would contradict
the supplied initial stopping step.  If it were nonempty but too short, the
last actual stop agrees with the corresponding bounded-trace state by the
pairwise-disjoint first-hit comparison, and the next bounded-trace transition
supplies a later post-exit source-black point, contradicting terminality of the
complete run.
-/
theorem hasAtLeast_of_boundedLocalUsedTrace
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace start : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) :
    TaoSection7Case3SourceStoppingRun.HasAtLeast steps (Rtrace + 1) := by
  by_contra hnot
  have hnot_len : ¬ Rtrace + 1 ≤ steps.length := by
    simpa [HasAtLeast, r] using hnot
  have hshort : steps.length < Rtrace + 1 := Nat.lt_of_not_ge hnot_len
  cases steps with
  | nil =>
      have hnoInitial :
          TaoSection7Case3NoInitialTriangleHitAfter pointAt family 0 :=
        TaoSection7Case3StoppingTerminal.noInitialTriangleHitAfter_of_nil
          hrun.terminal_condition
      exact hnoInitial st0.q hinit.first_hit.1 hinit.first_hit.2.1
  | cons head rest =>
      cases head with
      | mk first Γ =>
          let k : ℕ := rest.length
          have hk_lt : k < Rtrace := by
            dsimp [k] at hshort ⊢
            simpa using Nat.succ_lt_succ_iff.mp hshort
          have htake_eq :
              ((first, Γ) :: rest).take (k + 1) =
                ((htrace.state 0).q, (htrace.state 0).old) ::
                  taoSection7Case3IndexedEncounterTail
                    (fun k => (htrace.state k).q)
                    (fun k => (htrace.state k).old) 0 k :=
            TaoSection7Case3StoppingPrefix.take_eq_boundedLocalUsedTrace_prefix_of_le
              (hpair := hpair) hrun.trace_prefix
              (Rtail := k) (Rtrace := Rtrace)
              (Nat.le_of_lt hk_lt)
              (by simp [k])
              hinit htrace
          have htake_self :
              ((first, Γ) :: rest).take (k + 1) = (first, Γ) :: rest := by
            simp [k]
          have hsteps_eq :
              (first, Γ) :: rest =
                ((htrace.state 0).q, (htrace.state 0).old) ::
                  taoSection7Case3IndexedEncounterTail
                    (fun k => (htrace.state k).q)
                    (fun k => (htrace.state k).old) 0 k := by
            rw [← htake_self]
            exact htake_eq
          have hlast_trace :
              TaoSection7Case3StoppingLast?
                  (((htrace.state 0).q, (htrace.state 0).old) ::
                    taoSection7Case3IndexedEncounterTail
                      (fun k => (htrace.state k).q)
                      (fun k => (htrace.state k).old) 0 k) =
                some ((htrace.state k).q, (htrace.state k).old) :=
            by
              simpa using
                taoSection7Case3StoppingLast?_cons_indexedTail
                  (fun k => (htrace.state k).q)
                  (fun k => (htrace.state k).old) 0 k
          have hlast_steps :
              TaoSection7Case3StoppingLast? ((first, Γ) :: rest) =
                some ((htrace.state k).q, (htrace.state k).old) := by
            rw [hsteps_eq]
            exact hlast_trace
          have hnoLater :
              TaoSection7Case3NoLaterBlackAfterExit
                (taoSection7SourceBlackInDomain n xi epsilon J)
                pointAt ((htrace.state k).old) :=
            TaoSection7Case3StoppingTerminal.noLaterBlackAfterExit_of_last?_eq_some
              hrun.terminal_condition hlast_steps
          let htrans := htrace.transition k hk_lt
          let hchosen := htrans.1.usedStep.step
          let hupdate := hchosen.update
          have hk_first : (htrace.state k).q < hupdate.first :=
            TaoSection7Case3OneStepRebasedSourceUpdateWithGap.q_lt_first
              hupdate
          have hfirst_pos : 0 < hupdate.first :=
            lt_of_le_of_lt (Nat.zero_le _) hk_first
          have hexit :
              (htrace.state k).old.cornerL < (pointAt hupdate.first).l :=
            hupdate.source.first_hit.2.1.1
          exact hnoLater hupdate.first hfirst_pos hexit
            hupdate.source.first_black

theorem tR?_eq_boundedLocalUsedTrace
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace start : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) :
    tR? steps (Rtrace + 1) = some ((htrace.state Rtrace).q) := by
  have hR :
      HasAtLeast steps (Rtrace + 1) :=
    hrun.hasAtLeast_of_boundedLocalUsedTrace hpair hinit htrace
  have hlen : Rtrace + 1 ≤ steps.length := by
    simpa [HasAtLeast, r] using hR
  have htake :
      steps.take (Rtrace + 1) =
        ((htrace.state 0).q, (htrace.state 0).old) ::
          taoSection7Case3IndexedEncounterTail
            (fun k => (htrace.state k).q)
            (fun k => (htrace.state k).old) 0 Rtrace :=
    TaoSection7Case3StoppingPrefix.take_eq_boundedLocalUsedTrace_prefix_of_le
      (hpair := hpair) hrun.trace_prefix
      (Rtail := Rtrace) (Rtrace := Rtrace) (Nat.le_refl Rtrace)
      hlen hinit htrace
  have htR_take :
      tR? (steps.take (Rtrace + 1)) (Rtrace + 1) =
        some ((htrace.state Rtrace).q) := by
    rw [htake]
    simpa using
      taoSection7Case3_tR?_cons_indexedTail_last
        (fun k => (htrace.state k).q)
        (fun k => (htrace.state k).old) 0 Rtrace
  simpa [tR?_take_self] using htR_take

theorem hasTWithinWindow_of_boundedLocalUsedTrace
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace start : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) :
    HasTWithinWindow steps (Rtrace + 1) P :=
  ⟨(htrace.state Rtrace).q,
    hrun.tR?_eq_boundedLocalUsedTrace hpair hinit htrace,
    htrace.endpoint_q_ltP hfirst0_ltP⟩

/--
Producer-facing Lemma 7.9/Markov lower-bound packet before the
`r >= R` specialization.

The source statement first gives a lower bound at `t_min(r,R)`.  The
`tMin_eq` field records that pre-specialization accessor directly as
`tR? steps (min (r steps) R)`, while `sourceWhite_sum_gt` keeps the raw
positive-offset source-white sum visible.  This is an input contract only: it
does not prove Lemma 7.9, the Markov estimate, or the outside-`FSlack`
probability bound.
-/
structure Lemma79MarkovSourceWhiteMinBound
    (pointAt : ℕ → TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt p))]
    (steps : List (ℕ × TaoSection7Triangle))
    (R threshold tMin : ℕ) : Prop where
  tMin_eq : tR? steps (min (r steps) R) = some tMin
  sourceWhite_sum_gt :
    threshold <
      (Finset.Icc 1 tMin).sum
        (fun p : ℕ =>
          if taoSection7SourceWhitePoint n xi epsilon (pointAt p) then
            1
          else
            0)

namespace Lemma79MarkovSourceWhiteMinBound

theorem sourceWhitePoint_sum_gt_threshold_of_tR?
    {pointAt : ℕ → TaoSection7Point}
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt p))]
    {steps : List (ℕ × TaoSection7Triangle)}
    {R threshold tMin t : ℕ}
    (h :
      Lemma79MarkovSourceWhiteMinBound
        pointAt n xi epsilon steps R threshold tMin)
    (_hRpos : 0 < R)
    (hR : HasAtLeast steps R)
    (htR : tR? steps R = some t) :
    threshold <
      (Finset.Icc 1 t).sum
        (fun p : ℕ =>
          if taoSection7SourceWhitePoint n xi epsilon (pointAt p) then
            1
          else
            0) := by
  have hminIndex : min (r steps) R = R := Nat.min_eq_right hR
  have htMin_at_R : tR? steps R = some tMin := by
    simpa [hminIndex] using h.tMin_eq
  have htMin_eq : tMin = t := by
    rw [htR] at htMin_at_R
    cases htMin_at_R
    rfl
  simpa [htMin_eq] using h.sourceWhite_sum_gt

/--
Pointwise shifted-`FSlack` complement and scalar-room producer for the
Lemma 7.9 min-bound socket.

This is still a source-facing input theorem: the caller supplies the moment
identity and the real scalar room.  The theorem only performs the Markov
complement algebra, logarithmic cutoff comparison, and Nat count transport
needed to fill `Lemma79MarkovSourceWhiteMinBound`.
-/
theorem of_shiftedFSlack_pointwise_room
    {Ω : Type*}
    {FSlack : Set Ω} {ω : Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {R threshold tMin lemma79MinCount lowerBound Amarkov : ℕ}
    {moment : Ω → ℝ}
    (hout : ω ∉ FSlack)
    (hFSlack :
      FSlack =
        {ω | (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon < moment ω})
    (hmoment_eq :
      moment ω =
        Real.exp
          (-(lemma79MinCount : ℝ) +
            epsilon * (min (r (steps ω)) R : ℝ)))
    (hscalar_room :
      (lowerBound : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
          epsilon <
        epsilon * (min (r (steps ω)) R : ℝ))
    (hthreshold : threshold ≤ lowerBound)
    (htMin_eq : tR? (steps ω) (min (r (steps ω)) R) = some tMin)
    (hcount_identity_min :
      lemma79MinCount =
        (Finset.Icc 1 tMin).sum
          (fun p : ℕ =>
            if taoSection7SourceWhitePoint n xi epsilon (pointAt ω p) then
              1
            else
              0)) :
    Lemma79MarkovSourceWhiteMinBound
      (pointAt ω) n xi epsilon (steps ω) R threshold tMin where
  tMin_eq := htMin_eq
  sourceWhite_sum_gt := by
    let k : ℕ := Amarkov + 2
    let tMinIndex : ℕ := min (r (steps ω)) R
    have hnot_cutoff :
        ¬ ((10 : ℝ) ^ k * Real.exp epsilon < moment ω) := by
      have hout' :
          ω ∉ {ω | (10 : ℝ) ^ (Amarkov + 2) *
              Real.exp epsilon < moment ω} := by
        simpa [hFSlack] using hout
      simpa [k] using hout'
    have hmoment_le_cutoff :
        moment ω ≤ (10 : ℝ) ^ k * Real.exp epsilon :=
      le_of_not_gt hnot_cutoff
    have hpow_exp :
        (10 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 10) := by
      calc
        (10 : ℝ) ^ k = (Real.exp (Real.log 10)) ^ k := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 10)]
        _ = Real.exp ((k : ℝ) * Real.log 10) :=
          (Real.exp_nat_mul (Real.log 10) k).symm
    have hcutoff_eq :
        (10 : ℝ) ^ k * Real.exp epsilon =
          Real.exp ((k : ℝ) * Real.log 10 + epsilon) := by
      rw [hpow_exp, ← Real.exp_add]
    have hexp_le :
        Real.exp
            (-(lemma79MinCount : ℝ) +
              epsilon * (tMinIndex : ℝ)) ≤
          Real.exp ((k : ℝ) * Real.log 10 + epsilon) := by
      simpa [hmoment_eq, hcutoff_eq, tMinIndex] using hmoment_le_cutoff
    have harg_le :
        -(lemma79MinCount : ℝ) + epsilon * (tMinIndex : ℝ) ≤
          (k : ℝ) * Real.log 10 + epsilon :=
      Real.exp_le_exp.mp hexp_le
    have hroom_local :
        (lowerBound : ℝ) + ((k : ℝ) * Real.log 10 + epsilon) <
          epsilon * (tMinIndex : ℝ) := by
      have hroom_base :
          (lowerBound : ℝ) + (k : ℝ) * Real.log 10 + epsilon <
            epsilon * (tMinIndex : ℝ) := by
        simpa [k, tMinIndex] using hscalar_room
      calc
        (lowerBound : ℝ) + ((k : ℝ) * Real.log 10 + epsilon)
            = (lowerBound : ℝ) + (k : ℝ) * Real.log 10 + epsilon := by
              ring
        _ < epsilon * (tMinIndex : ℝ) := hroom_base
    have hlower_real : (lowerBound : ℝ) < (lemma79MinCount : ℝ) := by
      linarith [harg_le, hroom_local]
    have hcount_lower : lowerBound < lemma79MinCount := by
      exact_mod_cast hlower_real
    have hsource_lower :
        lowerBound <
          (Finset.Icc 1 tMin).sum
            (fun p : ℕ =>
              if taoSection7SourceWhitePoint n xi epsilon (pointAt ω p) then
                1
              else
                0) := by
      simpa [hcount_identity_min] using hcount_lower
    exact lt_of_le_of_lt hthreshold hsource_lower

end Lemma79MarkovSourceWhiteMinBound

/--
Source-facing pin for the repaired Lemma 7.9 tail statistic.

The global Markov moment is the repaired tail statistic, not the printed
unconditional `t_min(r,R)` statistic.  On samples with `r >= R` this statistic
reduces to the local exponential moment used by the pointwise min-bound socket.
-/
structure Lemma79RepairedTailOnRGeR
    {Ω : Type*}
    (steps : Ω → List (ℕ × TaoSection7Triangle))
    (R : ℕ)
    (tailCount : Ω → ℕ)
    (moment : Ω → ℝ)
    (epsilon : ℝ) : Prop where
  tail_moment_eq :
    ∀ ω : Ω,
      moment ω =
        if R ≤ TaoSection7Case3SourceStoppingRun.r (steps ω) then
          Real.exp (-(tailCount ω : ℝ) + epsilon * (R : ℝ))
        else
          0

namespace Lemma79RepairedTailOnRGeR

theorem moment_eq_min_of_r_ge
    {Ω : Type*}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {R : ℕ}
    {tailCount : Ω → ℕ}
    {moment : Ω → ℝ}
    {epsilon : ℝ}
    (h : Lemma79RepairedTailOnRGeR steps R tailCount moment epsilon)
    (ω : Ω)
    (hrge : R ≤ TaoSection7Case3SourceStoppingRun.r (steps ω)) :
    moment ω =
      Real.exp
        (-(tailCount ω : ℝ) +
          epsilon * (min (TaoSection7Case3SourceStoppingRun.r (steps ω)) R : ℝ)) := by
  rw [h.tail_moment_eq, ite_eq_left hrge]
  have hrge_real :
      (R : ℝ) ≤ (TaoSection7Case3SourceStoppingRun.r (steps ω) : ℝ) := by
    exact_mod_cast hrge
  rw [min_eq_right hrge_real]

end Lemma79RepairedTailOnRGeR

/--
Shared source-facing repaired Lemma 7.9 packet for the shifted `FSlack` gate.

This record ties the global PMF event and the pointwise min-bound complement
to the same repaired tail moment, event definition, `steps`, and `pointAt`.
It still contains source-facing hypotheses: the moment construction,
expectation bound, scalar room, threshold comparison, `t_min` accessor, and
source-white count identity are supplied rather than proved here.
-/
structure Lemma79SourceFSlackMomentPacket
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (FSlack : Set Ω)
    (pointAt : Ω → ℕ → TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    [∀ ω : Ω,
      DecidablePred
        (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    (steps : Ω → List (ℕ × TaoSection7Triangle))
    (R threshold Amarkov Aweight : ℕ)
    (tMin lemma79MinCount lowerBound : Ω → ℕ)
    (moment : Ω → ℝ) : Prop where
  Amarkov_eq : Amarkov = Aweight + 1
  R_pos : 0 < R
  repaired_tail_on_r_ge_R :
    Lemma79RepairedTailOnRGeR steps R lemma79MinCount moment epsilon
  FSlack_eq :
    FSlack =
      {ω | (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon < moment ω}
  moment_nonneg : ∀ ω : Ω, 0 ≤ moment ω
  repaired_tail_expectation_le : pmfExpectation μ moment ≤ Real.exp epsilon
  scalar_room :
    ∀ ω : Ω,
      R ≤ TaoSection7Case3SourceStoppingRun.r (steps ω) →
      (lowerBound ω : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
          epsilon <
        epsilon * (min (TaoSection7Case3SourceStoppingRun.r (steps ω)) R : ℝ)
  threshold_compare_min : ∀ ω : Ω, threshold ≤ lowerBound ω
  tMin_eq_on_r_ge :
    ∀ ω : Ω,
      R ≤ TaoSection7Case3SourceStoppingRun.r (steps ω) →
      TaoSection7Case3SourceStoppingRun.tR? (steps ω) R = some (tMin ω)
  count_identity_on_r_ge :
    ∀ ω : Ω,
      R ≤ TaoSection7Case3SourceStoppingRun.r (steps ω) →
      lemma79MinCount ω =
        (Finset.Icc 1 (tMin ω)).sum
          (fun p : ℕ =>
            if taoSection7SourceWhitePoint n xi epsilon (pointAt ω p) then
              1
            else
              0)

namespace Lemma79SourceFSlackMomentPacket

theorem fSlackBudget
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {FSlack : Set Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [∀ ω : Ω,
      DecidablePred
        (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {R threshold Amarkov Aweight : ℕ}
    {tMin lemma79MinCount lowerBound : Ω → ℕ}
    {moment : Ω → ℝ}
    (h :
      Lemma79SourceFSlackMomentPacket
        μ FSlack pointAt n xi epsilon steps R threshold Amarkov Aweight
        tMin lemma79MinCount lowerBound moment) :
    pmfProb μ FSlack ≤ 1 / ((10 : ℝ) ^ (Aweight + 3)) :=
  taoSection7Lemma79_fSlackBudget_of_expect
    μ FSlack moment Amarkov Aweight epsilon h.Amarkov_eq h.FSlack_eq
    h.moment_nonneg h.repaired_tail_expectation_le

theorem minBound
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {FSlack : Set Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [∀ ω : Ω,
      DecidablePred
        (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {R threshold Amarkov Aweight : ℕ}
    {tMin lemma79MinCount lowerBound : Ω → ℕ}
    {moment : Ω → ℝ}
    (h :
      Lemma79SourceFSlackMomentPacket
        μ FSlack pointAt n xi epsilon steps R threshold Amarkov Aweight
        tMin lemma79MinCount lowerBound moment)
    (ω : Ω) (hout : ω ∉ FSlack)
    (hrge : R ≤ TaoSection7Case3SourceStoppingRun.r (steps ω)) :
    Lemma79MarkovSourceWhiteMinBound
      (pointAt ω) n xi epsilon (steps ω) R threshold (tMin ω) := by
  have htMin_eq :
      TaoSection7Case3SourceStoppingRun.tR? (steps ω)
          (min (TaoSection7Case3SourceStoppingRun.r (steps ω)) R) =
        some (tMin ω) := by
    have hmin :
        min (TaoSection7Case3SourceStoppingRun.r (steps ω)) R = R :=
      Nat.min_eq_right hrge
    simpa [hmin] using h.tMin_eq_on_r_ge ω hrge
  exact
    Lemma79MarkovSourceWhiteMinBound.of_shiftedFSlack_pointwise_room
    (FSlack := FSlack) (ω := ω) (pointAt := pointAt) (steps := steps)
    (R := R) (threshold := threshold) (tMin := tMin ω)
    (lemma79MinCount := lemma79MinCount ω)
    (lowerBound := lowerBound ω) (Amarkov := Amarkov) (moment := moment)
    hout h.FSlack_eq
    (h.repaired_tail_on_r_ge_R.moment_eq_min_of_r_ge ω hrge)
    (h.scalar_room ω hrge)
    (h.threshold_compare_min ω) htMin_eq
    (h.count_identity_on_r_ge ω hrge)

end Lemma79SourceFSlackMomentPacket

/--
Pointwise producer-facing inputs for the Lemma 7.9/Markov min-bound socket.

This record does not prove the analytic estimates.  It keeps the future source
producer honest about the pieces it must supply: the outside-`FSlack` sample,
the `R = floor(A^2 / epsilon^4)` floor sandwich, the Lemma 7.9 moment bound,
the `FSlack` cutoff event, the outside-`FSlack` Markov/count lower bound at
`t_min(r,R)`, the count identity to the raw positive-offset source-white sum,
and the comparison to the Lean threshold.
-/
structure Lemma79MarkovSourceWhiteMinBoundInputs
    {Ω : Type*}
    (FSlack : Set Ω) (ω : Ω)
    (pointAt : Ω → ℕ → TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    (steps : Ω → List (ℕ × TaoSection7Triangle))
    (R threshold tMin lemma79MinCount lowerBound Aweight : ℕ)
    (moment momentUpper markovCutoff : ℝ) : Prop where
  outside_FSlack : ω ∉ FSlack
  R_floor_lower :
    (R : ℝ) ≤ ((Aweight : ℝ) ^ 2) / (epsilon ^ 4)
  R_floor_upper :
    ((Aweight : ℝ) ^ 2) / (epsilon ^ 4) < (R : ℝ) + 1
  lemma79_mgf_min : moment ≤ momentUpper
  FSlack_def : ω ∈ FSlack ↔ markovCutoff < moment
  markov_count_lower_of_not_FSlack :
    ω ∉ FSlack → lowerBound < lemma79MinCount
  threshold_compare_min : threshold ≤ lowerBound
  tMin_eq : tR? (steps ω) (min (r (steps ω)) R) = some tMin
  count_identity_min :
    lemma79MinCount =
      (Finset.Icc 1 tMin).sum
        (fun p : ℕ =>
          if taoSection7SourceWhitePoint n xi epsilon (pointAt ω p) then
            1
          else
            0)

namespace Lemma79MarkovSourceWhiteMinBoundInputs

theorem to_minBound
    {Ω : Type*}
    {FSlack : Set Ω} {ω : Ω}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {R threshold tMin lemma79MinCount lowerBound Aweight : ℕ}
    {moment momentUpper markovCutoff : ℝ}
    (h :
      Lemma79MarkovSourceWhiteMinBoundInputs
        FSlack ω pointAt n xi epsilon steps R threshold tMin
        lemma79MinCount lowerBound Aweight moment momentUpper markovCutoff) :
    Lemma79MarkovSourceWhiteMinBound
      (pointAt ω) n xi epsilon (steps ω) R threshold tMin where
  tMin_eq := h.tMin_eq
  sourceWhite_sum_gt := by
    have hcount_lower : lowerBound < lemma79MinCount :=
      h.markov_count_lower_of_not_FSlack h.outside_FSlack
    have hsource_lower :
        lowerBound <
          (Finset.Icc 1 tMin).sum
            (fun p : ℕ =>
              if taoSection7SourceWhitePoint n xi epsilon (pointAt ω p) then
                1
              else
                0) := by
      simpa [h.count_identity_min] using hcount_lower
    exact lt_of_le_of_lt h.threshold_compare_min hsource_lower

end Lemma79MarkovSourceWhiteMinBoundInputs

theorem sourceWhitePoint_sum_gt_threshold_of_boundedLocalUsedTrace_lemma79
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt p))]
    {P threshold base Kcut Rtrace start tMin : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0)
    (hlemma79 :
      Lemma79MarkovSourceWhiteMinBound
        pointAt n xi epsilon steps (Rtrace + 1) threshold tMin) :
    threshold <
      (Finset.Icc 1 ((htrace.state Rtrace).q)).sum
        (fun p : ℕ =>
          if taoSection7SourceWhitePoint n xi epsilon (pointAt p) then
            1
          else
            0) := by
  have hR :
      HasAtLeast steps (Rtrace + 1) :=
    hrun.hasAtLeast_of_boundedLocalUsedTrace hpair hinit htrace
  have htR :
      tR? steps (Rtrace + 1) = some ((htrace.state Rtrace).q) :=
    hrun.tR?_eq_boundedLocalUsedTrace hpair hinit htrace
  exact
    hlemma79.sourceWhitePoint_sum_gt_threshold_of_tR?
      (Nat.succ_pos Rtrace) hR htR

theorem many_positive_of_boundedLocalUsedTrace_count_identity
    {W : ℕ → Prop} [DecidablePred W]
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace start lemma79Count : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0)
    (hcount :
      lemma79Count =
        taoSection7Case3PositiveWhiteCount W ((htrace.state Rtrace).q))
    (hmany : threshold < lemma79Count) :
    ∀ t : ℕ,
      tR? steps (Rtrace + 1) = some t →
        threshold < taoSection7Case3PositiveWhiteCount W t := by
  intro t ht
  have htR :
      tR? steps (Rtrace + 1) = some ((htrace.state Rtrace).q) :=
    hrun.tR?_eq_boundedLocalUsedTrace hpair hinit htrace
  rw [htR] at ht
  cases ht
  simpa [hcount] using hmany

theorem many_positive_of_boundedLocalUsedTrace_sourceWhitePoint_sum
    {W : ℕ → Prop} [DecidablePred W]
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt p))]
    {P threshold base Kcut Rtrace start : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0)
    (hsource :
      threshold <
        (Finset.Icc 1 ((htrace.state Rtrace).q)).sum
          (fun p : ℕ =>
            if taoSection7SourceWhitePoint n xi epsilon (pointAt p) then
              1
            else
              0)) :
    ∀ t : ℕ,
      tR? steps (Rtrace + 1) = some t →
        threshold < taoSection7Case3PositiveWhiteCount W t := by
  intro t ht
  have htR :
      tR? steps (Rtrace + 1) = some ((htrace.state Rtrace).q) :=
    hrun.tR?_eq_boundedLocalUsedTrace hpair hinit htrace
  rw [htR] at ht
  cases ht
  exact
    hfacts.threshold_lt_positiveWhiteCount_of_sourceWhitePoint_sum
      (htrace.endpoint_q_ltP hfirst0_ltP) hsource

theorem not_low_window_of_boundedLocalUsedTrace_many_positive
    {W : ℕ → Prop} [DecidablePred W]
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace start : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0)
    (hmany :
      ∀ t : ℕ,
        tR? steps (Rtrace + 1) = some t →
          threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  not_low_window_of_hasTWithinWindow_many_positive
    (W := W) (steps := steps) (R := Rtrace + 1) (P := P)
    (threshold := threshold)
    (hrun.hasTWithinWindow_of_boundedLocalUsedTrace
      hpair hinit hfirst0_ltP htrace)
    hmany

theorem not_low_window_of_boundedLocalUsedTrace_count_identity
    {W : ℕ → Prop} [DecidablePred W]
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace start lemma79Count : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0)
    (hcount :
      lemma79Count =
        taoSection7Case3PositiveWhiteCount W ((htrace.state Rtrace).q))
    (hmany : threshold < lemma79Count) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  hrun.not_low_window_of_boundedLocalUsedTrace_many_positive
    hpair hinit hfirst0_ltP htrace
    (hrun.many_positive_of_boundedLocalUsedTrace_count_identity
      hpair hinit htrace hcount hmany)

theorem not_low_window_of_boundedLocalUsedTrace_sourceWhitePoint_sum
    {W : ℕ → Prop} [DecidablePred W]
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt p))]
    {P threshold base Kcut Rtrace start : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hrun :
      TaoSection7Case3SourceStoppingRun
        (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family steps)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts
        W pointAt n J xi epsilon P)
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0)
    (hsource :
      threshold <
        (Finset.Icc 1 ((htrace.state Rtrace).q)).sum
          (fun p : ℕ =>
            if taoSection7SourceWhitePoint n xi epsilon (pointAt p) then
              1
            else
              0)) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold :=
  hrun.not_low_window_of_boundedLocalUsedTrace_many_positive
    hpair hinit hfirst0_ltP htrace
    (hrun.many_positive_of_boundedLocalUsedTrace_sourceWhitePoint_sum
      hpair hinit hfacts hfirst0_ltP htrace hsource)

end TaoSection7Case3SourceStoppingRun

namespace TaoSection7Case3ActualRunSourceIdentity

/--
Produce the take-prefix equality consumed by the bounded-trace endpoint
adapter.

This is the finite compatibility bridge from an actual stopping run to a
bounded local-used trace.  It still assumes the bounded trace and the shared
initial stopping step; it does not construct either from source probability
data.
-/
theorem take_eq_boundedLocalUsedTrace
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start tR lemma79Count : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family n J xi epsilon P steps (Rtail + 1) tR
        lemma79Count)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    steps.take (Rtail + 1) =
      ((htrace.state 0).q, (htrace.state 0).old) ::
        taoSection7Case3IndexedEncounterTail
          (fun k => (htrace.state k).q)
          (fun k => (htrace.state k).old) 0 Rtail := by
  have hlen : Rtail + 1 ≤ steps.length := by
    simpa [TaoSection7Case3SourceStoppingRun.HasAtLeast,
      TaoSection7Case3SourceStoppingRun.r] using h.R_le_r
  exact
    TaoSection7Case3StoppingPrefix.take_eq_boundedLocalUsedTrace_prefix
      (hpair := hpair) h.source_run.trace_prefix hlen hinit htrace

/--
Endpoint-window extractor from an actual run and a bounded local-used trace,
with the take-prefix equality supplied by
`take_eq_boundedLocalUsedTrace`.
-/
theorem tR_ltP_of_boundedLocalUsedTrace
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtail start tR lemma79Count : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family n J xi epsilon P steps (Rtail + 1) tR
        lemma79Count)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0) :
    tR < P :=
  h.tR_ltP_of_boundedLocalUsedTrace_take_eq hinit hfirst0_ltP htrace
    (h.take_eq_boundedLocalUsedTrace hpair hinit htrace)

/--
Checked bridge from the Lemma 7.9/Markov min-bound socket to the `hmany`
input consumed by the low-window contradiction.

This composes only already-local infrastructure: specialization of the
min-bound source-white sum to `t_R`, all-window source/`W` transport, and the
actual-run count identity.  It does not prove the Lemma 7.9 producer or the
global `FSlack` probability budget.
-/
theorem manyWhite_of_lemma79MinBound
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt p))]
    {P R tR lemma79Count threshold tMin : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W black pointAt family n J xi epsilon P steps R tR
        lemma79Count)
    (htR_ltP : tR < P)
    (hlemma79 :
      TaoSection7Case3SourceStoppingRun.Lemma79MarkovSourceWhiteMinBound
        pointAt n xi epsilon steps R threshold tMin) :
    threshold < lemma79Count := by
  have hsource :
      threshold <
        (Finset.Icc 1 tR).sum
          (fun p : ℕ =>
            if taoSection7SourceWhitePoint n xi epsilon (pointAt p) then
              1
            else
              0) :=
    hlemma79.sourceWhitePoint_sum_gt_threshold_of_tR?
      h.R_pos h.R_le_r h.tR_eq
  have htR_positive :
      threshold < taoSection7Case3PositiveWhiteCount W tR :=
    h.sameW.threshold_lt_positiveWhiteCount_of_sourceWhitePoint_sum
      htR_ltP hsource
  simpa [h.count_identity] using htR_positive

/--
Bounded-trace specialization of `manyWhite_of_lemma79MinBound`.

The bounded trace supplies the endpoint fact `t_R < P`; the Lemma 7.9 socket
still remains an explicit input.
-/
theorem manyWhite_of_boundedLocalUsedTrace_lemma79_minBound
    {sourceAt : ℕ → TaoSection7Point} {restart : ℕ}
    {W : ℕ → Prop} [DecidablePred W]
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [DecidablePred
      (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt p))]
    {P threshold base Kcut Rtail start tR lemma79Count tMin : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    {st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        sourceAt restart W (taoSection7SourceBlackInDomain n xi epsilon J)
        pointAt family n J xi epsilon P steps (Rtail + 1) tR
        lemma79Count)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family st0.q st0.old)
    (hfirst0_ltP : st0.q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtail) (start := start) st0)
    (hlemma79 :
      TaoSection7Case3SourceStoppingRun.Lemma79MarkovSourceWhiteMinBound
        pointAt n xi epsilon steps (Rtail + 1) threshold tMin) :
    threshold < lemma79Count :=
  h.manyWhite_of_lemma79MinBound
    (h.tR_ltP_of_boundedLocalUsedTrace
      hpair hinit hfirst0_ltP htrace)
    hlemma79

/--
Bounded-trace specialization of the repaired-tail Lemma 7.9 source packet.

The actual-run identity supplies the `R <= r` branch needed by the packet's
pointwise projection, while the bounded trace supplies the endpoint window
fact `t_R < P`.  The repaired expectation, source moment construction, and
scalar-room fields remain inside the supplied packet.
-/
theorem manyWhite_of_boundedLocalUsedTrace_lemma79_sourcePacket
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {FSlack : Set Ω}
    {sourceAt : Ω → ℕ → TaoSection7Point} {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {family : Set TaoSection7Triangle}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {Accepts : Ω → ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Ω → Set ℕ} {allowedFin : Ω → Finset ℕ}
    {bound : Ω → ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [∀ ω : Ω,
      DecidablePred
        (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    {P threshold base Kcut Rtail start Amarkov Aweight : ℕ}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count tMin : Ω → ℕ}
    {lemma79MinCount lowerBound : Ω → ℕ}
    {moment : Ω → ℝ}
    {st0 :
      ∀ ω : Ω,
        TaoSection7Case3ActiveSourceStateWithGap
          (W ω) family (pointAt ω) (bound ω) n J xi epsilon P threshold
          (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    (hpacket :
      TaoSection7Case3SourceStoppingRun.Lemma79SourceFSlackMomentPacket
        μ FSlack pointAt n xi epsilon steps (Rtail + 1) threshold
        Amarkov Aweight tMin lemma79MinCount lowerBound moment)
    (ω : Ω)
    (h :
      TaoSection7Case3ActualRunSourceIdentity
        (sourceAt ω) (restart ω) (W ω)
        (taoSection7SourceBlackInDomain n xi epsilon J)
        (pointAt ω) family n J xi epsilon P (steps ω)
        (Rtail + 1) (tR ω) (lemma79Count ω))
    (hnotF : ω ∉ FSlack)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      TaoSection7Case3InitialStoppingStep
        (pointAt ω) family (st0 ω).q (st0 ω).old)
    (hfirst0_ltP : (st0 ω).q < P)
    (htrace :
      TaoSection7Case3BoundedLocalUsedTrace
        (W := W ω) (family := family) (pointAt := pointAt ω)
        (Accepts := Accepts ω) (used := used ω)
        (allowedFin := allowedFin ω) (bound := bound ω)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon)
        (P := P) (threshold := threshold) (base := base) (Kcut := Kcut)
        (R := Rtail) (start := start) (st0 ω)) :
    threshold < lemma79Count ω :=
  h.manyWhite_of_boundedLocalUsedTrace_lemma79_minBound
    hpair hinit hfirst0_ltP htrace
    (hpacket.minBound ω hnotF h.R_le_r_steps)

end TaoSection7Case3ActualRunSourceIdentity

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79SourceFSlackMomentPacket

/-- Source-white count through the supplied `t_min` accessor. -/
def sourceWhiteCountAtTMin
    {Ω : Type*}
    (pointAt : Ω → ℕ → TaoSection7Point)
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    [∀ ω : Ω,
      DecidablePred
        (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    (tMin : Ω → ℕ) : Ω → ℕ :=
  fun ω =>
    (Finset.Icc 1 (tMin ω)).sum
      (fun p : ℕ =>
        if taoSection7SourceWhitePoint n xi epsilon (pointAt ω p) then
          1
        else
          0)

/-- Repaired tail moment used by the source-facing Lemma 7.9 packet. -/
noncomputable def repairedTailMoment
    {Ω : Type*}
    (steps : Ω → List (ℕ × TaoSection7Triangle))
    (R : ℕ)
    (tailCount : Ω → ℕ)
    (epsilon : ℝ) : Ω → ℝ :=
  fun ω =>
    if R ≤ r (steps ω) then
      Real.exp (-(tailCount ω : ℝ) + epsilon * (R : ℝ))
    else
      0

/-- Strict shifted `FSlack` event attached to the repaired tail moment. -/
noncomputable def shiftedFSlackEvent
    {Ω : Type*}
    (steps : Ω → List (ℕ × TaoSection7Triangle))
    (R : ℕ)
    (tailCount : Ω → ℕ)
    (Amarkov : ℕ)
    (epsilon : ℝ) : Set Ω :=
  {ω | (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon <
    repairedTailMoment steps R tailCount epsilon ω}

/-- Deterministic `t_min` accessor extracted from `tR?`, with default unused. -/
def tMinIndex
    {Ω : Type*}
    (steps : Ω → List (ℕ × TaoSection7Triangle))
    (R : ℕ) : Ω → ℕ :=
  fun ω => (tR? (steps ω) (min (r (steps ω)) R)).getD 0

theorem tMinIndex_min_pos_of_isSome
    {Ω : Type*}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {R : ℕ}
    (h :
      ∀ ω : Ω,
        (tR? (steps ω) (min (r (steps ω)) R)).isSome = true) :
    ∀ ω : Ω, 0 < min (r (steps ω)) R := by
  intro ω
  exact tR?_isSome_pos (h ω)

/--
Reduce the packet's scalar-room field to a cleaner `R`-room premise.

This is only the `min(r,R) = R` rewrite under the branch evidence `R <= r`.
It does not prove the large-`Aweight`/floor inequality that must eventually
produce the `R`-room bound.
-/
theorem scalar_room_of_R_room
    {Ω : Type*}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {R Amarkov : ℕ}
    {lowerBound : Ω → ℕ}
    {epsilon : ℝ}
    (hroomR :
      ∀ ω : Ω,
        (lowerBound ω : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
            epsilon <
          epsilon * (R : ℝ)) :
    ∀ ω : Ω,
      R ≤ r (steps ω) →
        (lowerBound ω : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
            epsilon <
          epsilon * (min (r (steps ω)) R : ℝ) := by
  intro ω hrge
  have hrge_real : (R : ℝ) ≤ (r (steps ω) : ℝ) := by
    exact_mod_cast hrge
  simpa [min_eq_right hrge_real] using hroomR ω

/--
Producer pilot for the repaired-tail Lemma 7.9 source packet.

The repaired tail moment, strict shifted `FSlack` event, and source-white count
are definitional here.  The analytic expectation estimate, the large-parameter
`R`-room inequality, threshold comparison, `0 < R`, and the branch-local
`t_min` accessor remain explicit producer obligations.
-/
theorem of_repairedTailMoment
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    {pointAt : Ω → ℕ → TaoSection7Point}
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [∀ ω : Ω,
      DecidablePred
        (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {R threshold Amarkov Aweight : ℕ}
    {tMin lowerBound : Ω → ℕ}
    (hAmarkov : Amarkov = Aweight + 1)
    (hR_pos : 0 < R)
    (hexpect :
      pmfExpectation μ
          (repairedTailMoment steps R
            (sourceWhiteCountAtTMin pointAt n xi epsilon tMin) epsilon) ≤
        Real.exp epsilon)
    (hroomR :
      ∀ ω : Ω,
        (lowerBound ω : ℝ) + ((Amarkov + 2 : ℕ) : ℝ) * Real.log 10 +
            epsilon <
          epsilon * (R : ℝ))
    (hthreshold : ∀ ω : Ω, threshold ≤ lowerBound ω)
    (htMin_eq_on_r_ge :
      ∀ ω : Ω,
        R ≤ r (steps ω) →
        tR? (steps ω) R = some (tMin ω)) :
    Lemma79SourceFSlackMomentPacket
      μ
      (shiftedFSlackEvent steps R
        (sourceWhiteCountAtTMin pointAt n xi epsilon tMin) Amarkov epsilon)
      pointAt n xi epsilon steps R threshold Amarkov Aweight tMin
      (sourceWhiteCountAtTMin pointAt n xi epsilon tMin) lowerBound
      (repairedTailMoment steps R
        (sourceWhiteCountAtTMin pointAt n xi epsilon tMin) epsilon) where
  Amarkov_eq := hAmarkov
  R_pos := hR_pos
  repaired_tail_on_r_ge_R :=
    { tail_moment_eq := by
        intro ω
        rfl }
  FSlack_eq := rfl
  moment_nonneg := by
    intro ω
    by_cases hR : R ≤ r (steps ω)
    · have hpos :
          0 <
            Real.exp
              (-(sourceWhiteCountAtTMin pointAt n xi epsilon tMin ω : ℝ) +
                epsilon * (R : ℝ)) :=
        Real.exp_pos _
      simpa [repairedTailMoment, hR] using hpos.le
    · simp [repairedTailMoment, hR]
  repaired_tail_expectation_le := hexpect
  scalar_room := scalar_room_of_R_room hroomR
  threshold_compare_min := hthreshold
  tMin_eq_on_r_ge := htMin_eq_on_r_ge
  count_identity_on_r_ge := by
    intro ω _hrge
    rfl

/--
Packet-namespaced actual-run consumer for the repaired-tail Lemma 7.9 source
packet.

For a fixed sample, the actual-run identity supplies the `R <= r` branch
needed by `minBound`; the endpoint fact `t_R < P` stays explicit.  This is the
narrow projection that feeds the existing `manyWhite` consumer without proving
the repaired expectation, source moment construction, endpoint control, or
scalar-room inputs.
-/
theorem manyWhite_of_actualRun
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {FSlack : Set Ω}
    {sourceAt : Ω → ℕ → TaoSection7Point} {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {black : Ω → TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : Ω → ℕ → TaoSection7Point}
    {n J P R threshold Amarkov Aweight : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [∀ ω : Ω,
      DecidablePred
        (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count tMin : Ω → ℕ}
    {lemma79MinCount lowerBound : Ω → ℕ}
    {moment : Ω → ℝ}
    (h :
      Lemma79SourceFSlackMomentPacket
        μ FSlack pointAt n xi epsilon steps R threshold Amarkov Aweight
        tMin lemma79MinCount lowerBound moment)
    (ω : Ω)
    (hidentity :
      TaoSection7Case3ActualRunSourceIdentity
        (sourceAt ω) (restart ω) (W ω) (black ω) (pointAt ω) family
        n J xi epsilon P (steps ω) R (tR ω) (lemma79Count ω))
    (htR_ltP : tR ω < P)
    (hnotF : ω ∉ FSlack) :
    threshold < lemma79Count ω :=
  hidentity.manyWhite_of_lemma79MinBound htR_ltP
    (h.minBound ω hnotF hidentity.R_le_r_steps)

end Lemma79SourceFSlackMomentPacket
end TaoSection7Case3SourceStoppingRun

/--
Low-white subset bridge whose endpoint half is derived directly from bounded
local-used traces.

This removes the separate `PrefixRInputs` and `steps.take` premises from the
outside-sample endpoint path.  It still assumes the actual-run identities,
bounded traces, initial stopping data, and Lemma 7.9-style many-white lower
bound.
-/
theorem taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_boundedLocalUsedTrace
    {Ω : Type*}
    {sourceAt : Ω → ℕ → TaoSection7Point}
    {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {Accepts : Ω → ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {family : Set TaoSection7Triangle}
    {used : Ω → Set ℕ} {allowedFin : Ω → Finset ℕ}
    {bound : Ω → ℕ → ℝ}
    {n J P threshold base Kcut Rtail start : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count : Ω → ℕ}
    {st0 :
      ∀ ω : Ω,
        TaoSection7Case3ActiveSourceStateWithGap
          (W ω) family (pointAt ω) (bound ω) n J xi epsilon P threshold
          (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    {EStarUsed FSlack : Set Ω}
    (hidentity :
      ∀ ω : Ω,
        TaoSection7Case3ActualRunSourceIdentity
          (sourceAt ω) (restart ω) (W ω)
          (taoSection7SourceBlackInDomain n xi epsilon J)
          (pointAt ω) family n J xi epsilon P (steps ω)
          (Rtail + 1) (tR ω) (lemma79Count ω))
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        TaoSection7Case3InitialStoppingStep
          (pointAt ω) family (st0 ω).q (st0 ω).old)
    (hfirst0_ltP :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack → (st0 ω).q < P)
    (htrace :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        TaoSection7Case3BoundedLocalUsedTrace
          (W := W ω) (family := family) (pointAt := pointAt ω)
          (Accepts := Accepts ω) (used := used ω)
          (allowedFin := allowedFin ω) (bound := bound ω)
          (n := n) (J := J) (xi := xi) (epsilon := epsilon)
          (P := P) (threshold := threshold) (base := base) (Kcut := Kcut)
          (R := Rtail) (start := start) (st0 ω))
    (hmany :
      ∀ ω : Ω, ω ∉ EStarUsed → ω ∉ FSlack →
        threshold < lemma79Count ω) :
    taoSection7Case3LowWhiteEvent W P threshold ⊆ EStarUsed ∪ FSlack := by
  refine
    taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity
      (hidentity := hidentity) ?_
  intro ω hnotE hnotF
  exact
    ⟨(hidentity ω).tR_ltP_of_boundedLocalUsedTrace
        hpair (hinit ω hnotE hnotF) (hfirst0_ltP ω hnotE hnotF)
        (htrace ω hnotE hnotF),
      hmany ω hnotE hnotF⟩

/--
Branch-local bounded-trace low-white subset bridge.

Unlike
`taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_boundedLocalUsedTrace`,
the endpoint and many-white inputs may use the low-white membership currently
being contradicted.  This matches the source Case 3 branch shape: trace
production is only required on samples that are low-white and outside the two
exceptional events.
-/
theorem taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_boundedLocalUsedTrace_onLowWhite
    {Ω : Type*}
    {sourceAt : Ω → ℕ → TaoSection7Point}
    {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {Accepts : Ω → ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {family : Set TaoSection7Triangle}
    {used : Ω → Set ℕ} {allowedFin : Ω → Finset ℕ}
    {bound : Ω → ℕ → ℝ}
    {n J P threshold base Kcut Rtail start : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count : Ω → ℕ}
    {st0 :
      ∀ ω : Ω,
        TaoSection7Case3ActiveSourceStateWithGap
          (W ω) family (pointAt ω) (bound ω) n J xi epsilon P threshold
          (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    {EStarUsed FSlack : Set Ω}
    (hidentity :
      ∀ ω : Ω,
        TaoSection7Case3ActualRunSourceIdentity
          (sourceAt ω) (restart ω) (W ω)
          (taoSection7SourceBlackInDomain n xi epsilon J)
          (pointAt ω) family n J xi epsilon P (steps ω)
          (Rtail + 1) (tR ω) (lemma79Count ω))
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          TaoSection7Case3InitialStoppingStep
            (pointAt ω) family (st0 ω).q (st0 ω).old)
    (hfirst0_ltP :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack → (st0 ω).q < P)
    (htrace :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          TaoSection7Case3BoundedLocalUsedTrace
            (W := W ω) (family := family) (pointAt := pointAt ω)
            (Accepts := Accepts ω) (used := used ω)
            (allowedFin := allowedFin ω) (bound := bound ω)
            (n := n) (J := J) (xi := xi) (epsilon := epsilon)
            (P := P) (threshold := threshold) (base := base) (Kcut := Kcut)
            (R := Rtail) (start := start) (st0 ω))
    (hmany :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          threshold < lemma79Count ω) :
    taoSection7Case3LowWhiteEvent W P threshold ⊆ EStarUsed ∪ FSlack := by
  refine taoSection7Case3_lowWhite_subset_EStarUsed_union_FSlack ?_
  intro ω hlow hnotE hnotF
  have htR_ltP : tR ω < P :=
    (hidentity ω).tR_ltP_of_boundedLocalUsedTrace
      hpair (hinit ω hlow hnotE hnotF)
      (hfirst0_ltP ω hlow hnotE hnotF)
      (htrace ω hlow hnotE hnotF)
  have hnotLow :
      ¬ taoSection7Case3WindowWhiteCount (W ω) P ≤ threshold :=
    (hidentity ω).not_low_window_of_tR_ltP_many_positive htR_ltP
      (hmany ω hlow hnotE hnotF)
  exact hnotLow (by
    simpa [taoSection7Case3LowWhiteEvent, taoSection7Case3LowWhite] using
      hlow)

/--
Low-white subset bridge from the repaired-tail Lemma 7.9 source packet on the
bounded-trace branch.

This composes the checked repaired-tail packet with the bounded-trace
actual-run route.  It supplies the packet's pointwise `R <= r` requirement
from the actual-run identity and leaves only the packet inputs, bounded-trace
construction, and endpoint initialization as external producers.
-/
theorem taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_boundedLocalUsedTrace_sourcePacket_onLowWhite
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {sourceAt : Ω → ℕ → TaoSection7Point}
    {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {Accepts : Ω → ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {family : Set TaoSection7Triangle}
    {used : Ω → Set ℕ} {allowedFin : Ω → Finset ℕ}
    {bound : Ω → ℕ → ℝ}
    {n J P threshold base Kcut Rtail start Amarkov Aweight : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    [∀ ω : Ω,
      DecidablePred
        (fun p : ℕ => taoSection7SourceWhitePoint n xi epsilon (pointAt ω p))]
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count tMin : Ω → ℕ}
    {lemma79MinCount lowerBound : Ω → ℕ}
    {moment : Ω → ℝ}
    {st0 :
      ∀ ω : Ω,
        TaoSection7Case3ActiveSourceStateWithGap
          (W ω) family (pointAt ω) (bound ω) n J xi epsilon P threshold
          (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    {EStarUsed FSlack : Set Ω}
    (hpacket :
      TaoSection7Case3SourceStoppingRun.Lemma79SourceFSlackMomentPacket
        μ FSlack pointAt n xi epsilon steps (Rtail + 1) threshold
        Amarkov Aweight tMin lemma79MinCount lowerBound moment)
    (hidentity :
      ∀ ω : Ω,
        TaoSection7Case3ActualRunSourceIdentity
          (sourceAt ω) (restart ω) (W ω)
          (taoSection7SourceBlackInDomain n xi epsilon J)
          (pointAt ω) family n J xi epsilon P (steps ω)
          (Rtail + 1) (tR ω) (lemma79Count ω))
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          TaoSection7Case3InitialStoppingStep
            (pointAt ω) family (st0 ω).q (st0 ω).old)
    (hfirst0_ltP :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack → (st0 ω).q < P)
    (htrace :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          TaoSection7Case3BoundedLocalUsedTrace
            (W := W ω) (family := family) (pointAt := pointAt ω)
            (Accepts := Accepts ω) (used := used ω)
            (allowedFin := allowedFin ω) (bound := bound ω)
            (n := n) (J := J) (xi := xi) (epsilon := epsilon)
            (P := P) (threshold := threshold) (base := base) (Kcut := Kcut)
            (R := Rtail) (start := start) (st0 ω)) :
    taoSection7Case3LowWhiteEvent W P threshold ⊆ EStarUsed ∪ FSlack := by
  refine
    taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_boundedLocalUsedTrace_onLowWhite
      (hidentity := hidentity) hpair hinit hfirst0_ltP htrace ?_
  intro ω hlow hnotE hnotF
  exact
    (hidentity ω).manyWhite_of_boundedLocalUsedTrace_lemma79_sourcePacket
      (hpacket := hpacket) ω hnotF hpair
      (hinit ω hlow hnotE hnotF)
      (hfirst0_ltP ω hlow hnotE hnotF)
      (htrace ω hlow hnotE hnotF)

/--
Construct a finite bounded local-used trace from an on-trace step producer.

The producer receives the current state only after the recursion has built it,
and also receives the propagated proof that the state lies under the
base-Kcut iterate bound.
-/
theorem taoSection7Case3_boundedLocalUsedTrace_of_statefulStep
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut R start : ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (h0 : st0.q ≤ start)
    (hstep :
      ∀ i : ℕ, i < R →
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold
            (taoSection7Case3ExitGapBoundWithBase base Kcut),
        st.q ≤
            ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i])
              start →
        Nonempty
          (TaoSection7Case3ChosenActiveLocalUsedStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts)
            (localAllowed :=
              taoSection7Case3LocalSelectedEnvelope
                (taoSection7Case3ExitGapBoundWithBase base Kcut)
                threshold st.q)
            (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st)) :
    Nonempty
      (TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := R) (start := start) st0) := by
  classical
  induction R generalizing st0 with
  | zero =>
      refine ⟨?_⟩
      exact
        { state := fun _i => st0
          state_zero := rfl
          transition := by
            intro i hi
            omega
          q_bound := by
            intro i hi
            have hi0 : i = 0 := by omega
            subst i
            simpa using h0 }
  | succ Rtail ih =>
      let hrec :=
        Classical.choice
          (ih st0 h0
            (fun i hi st hbound => hstep i (by omega) st hbound))
      let lastState :=
        hrec.state Rtail
      let lastStep :=
        Classical.choice
          (hstep Rtail (by omega) lastState
            (by
              simpa [lastState] using
                hrec.q_bound Rtail (Nat.le_refl Rtail)))
      let nextState :=
        TaoSection7Case3ChosenActiveStepWithGap.nextState
          ((lastStep).usedStep.step)
      let state :
          ℕ →
            TaoSection7Case3ActiveSourceStateWithGap
              W family pointAt bound n J xi epsilon P threshold
              (taoSection7Case3ExitGapBoundWithBase base Kcut) :=
        fun i =>
          if hle : i ≤ Rtail then
            hrec.state i
          else
            nextState
      refine ⟨?_⟩
      exact
        { state := state
          state_zero := by
            have hle0 : 0 ≤ Rtail := Nat.zero_le Rtail
            simpa [state, hle0] using hrec.state_zero
          transition := by
            intro i hi
            by_cases hlt : i < Rtail
            · have hle_succ : i + 1 ≤ Rtail := Nat.succ_le_of_lt hlt
              have hstate_i : state i = hrec.state i := by
                simp [state, Nat.le_of_lt hlt]
              have hstate_succ : state (i + 1) = hrec.state (i + 1) := by
                simp [state, hle_succ]
              rw [hstate_i, hstate_succ]
              exact hrec.transition i hlt
            · have hi_eq : i = Rtail := by omega
              subst i
              have hnot : ¬ Rtail + 1 ≤ Rtail := by omega
              have hstate_i : state Rtail = hrec.state Rtail := by
                simp [state]
              have hstate_succ : state (Rtail + 1) = nextState := by
                simp [state, hnot]
              rw [hstate_i, hstate_succ]
              refine ⟨lastStep, ?_⟩
              rfl
          q_bound := by
            intro i hi
            by_cases hle : i ≤ Rtail
            · simpa [state, hle] using hrec.q_bound i hle
            · have hi_eq : i = Rtail + 1 := by omega
              subst i
              have hnot : ¬ Rtail + 1 ≤ Rtail := by omega
              have hfirst :
                  ((lastStep).usedStep.step.update.first) ≤
                    taoSection7Case3BaseKcutNextBound base Kcut threshold
                      lastState.q :=
                TaoSection7Case3ChosenActiveLocalUsedStepWithGap.first_le_baseKcutNextBound
                  (base := base) (Kcut := Kcut) (hstep := lastStep)
              have hmono :
                  taoSection7Case3BaseKcutNextBound base Kcut threshold
                      lastState.q ≤
                    taoSection7Case3BaseKcutNextBound base Kcut threshold
                      (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtail])
                        start) :=
                taoSection7Case3BaseKcutNextBound_mono base Kcut threshold
                  (by
                    simpa [lastState] using
                      hrec.q_bound Rtail (Nat.le_refl Rtail))
              have hnext :
                  nextState.q =
                    (lastStep).usedStep.step.update.first := by
                rfl
              rw [show state (Rtail + 1) = nextState by
                simp [state, hnot]]
              rw [hnext]
              exact le_trans hfirst (by
                simpa [Function.iterate_succ_apply'] using hmono) }

/--
Source-facing fixed-carrier instantiation of the bounded local-used trace
recursor.

This removes the abstract bounded `hstep` premise by calling the checked
base-Kcut range one-step constructor at each reached state.  The room and
acceptance inputs are still explicit per-state sockets; producing them from the
source process remains the next gate.
-/
theorem taoSection7Case3_boundedLocalUsedTrace_of_baseKcutRange_notEStar_sandwich
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut R start : ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (h0 : st0.q ≤ start)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
            start + 1))
        bound)
    (hω : ω ∉ EStarUsed)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ i : ℕ, i < R →
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family (pointAtΩ ω) bound n J xi epsilon P threshold
            (taoSection7Case3ExitGapBoundWithBase base Kcut),
        st.q ≤
            ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i])
              start →
        ∀ first : ℕ, st.q < first → first < P →
          taoSection7Case3ExitRoom
            (taoSection7Case3LaterSearchBound
              (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold)
            P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (haccept :
      ∀ i : ℕ, i < R →
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family (pointAtΩ ω) bound n J xi epsilon P threshold
            (taoSection7Case3ExitGapBoundWithBase base Kcut),
        st.q ≤
            ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i])
              start →
        ∀ first Γ,
          first < P →
          taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
          TaoSection7Case3FirstAfterTriangleHitFrom
            (pointAtΩ ω) family st.old st.q first →
          Γ ∈ family →
          Γ.Mem ((pointAtΩ ω) first) →
          Γ ≠ st.old →
          Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts)
        (used :=
          {p : ℕ |
            p ∈ Finset.range
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
                start + 1)})
        (allowedFin :=
          Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
              start + 1))
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := R) (start := start) st0) := by
  exact
    taoSection7Case3_boundedLocalUsedTrace_of_statefulStep
      (W := W) (family := family) (pointAt := pointAtΩ ω)
      (Accepts := Accepts)
      (used :=
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
              start + 1)})
      (allowedFin :=
        Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R])
            start + 1))
      (bound := bound) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (base := base) (Kcut := Kcut) (R := R) (start := start)
      st0 h0
      (fun i hi st htrace_le =>
        taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_baseKcutRange_notEStar_sandwich
          (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
          (Accepts := Accepts) (EStarUsed := EStarUsed)
          (bound := bound) (n := n) (J := J) (xi := xi)
          (epsilon := epsilon) (P := P) (threshold := threshold)
          (base := base) (Kcut := Kcut) (R := R) (start := start)
          (i := i) st sandwich hω htrace_le (Nat.succ_le_of_lt hi)
          hscale hlow hcover (hroom_next i hi st htrace_le) hfacts
          (haccept i hi st htrace_le))

/--
Room-depth split fixed-carrier bounded trace wrapper.

The support carrier and trace length are governed by `Rtrace`, while the
deterministic room hypothesis is allowed to run to `Rroom`.  The explicit
`Rtrace + 1 ≤ Rroom` margin is what lets the final selected transition obtain
successor room from the local selected-envelope room lemma without replacing
Tao's `Rtrace` selected stops by `Rtrace - 1`.
-/
theorem taoSection7Case3_boundedLocalUsedTrace_of_baseKcutRange_notEStar_sandwich_roomDepth
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace Rroom start : ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (h0 : st0.q ≤ start)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
        bound)
    (hω : ω ∉ EStarUsed)
    (hroom_iter :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold Rroom start P)
    (hroom_depth : Rtrace + 1 ≤ Rroom)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (haccept :
      ∀ i : ℕ, i < Rtrace →
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family (pointAtΩ ω) bound n J xi epsilon P threshold
            (taoSection7Case3ExitGapBoundWithBase base Kcut),
        st.q ≤
            ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i])
              start →
        ∀ first Γ,
          first < P →
          taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
          TaoSection7Case3FirstAfterTriangleHitFrom
            (pointAtΩ ω) family st.old st.q first →
          Γ ∈ family →
          Γ.Mem ((pointAtΩ ω) first) →
          Γ ≠ st.old →
          Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts)
        (used :=
          {p : ℕ |
            p ∈ Finset.range
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
                start + 1)})
        (allowedFin :=
          Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1))
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) := by
  exact
    taoSection7Case3_boundedLocalUsedTrace_of_statefulStep
      (W := W) (family := family) (pointAt := pointAtΩ ω)
      (Accepts := Accepts)
      (used :=
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)})
      (allowedFin :=
        Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
      (bound := bound) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (base := base) (Kcut := Kcut) (R := Rtrace) (start := start)
      st0 h0
      (fun i hi st htrace_le =>
        taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_baseKcutRange_notEStar_sandwich_roomDepth
          (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
          (Accepts := Accepts) (EStarUsed := EStarUsed)
          (bound := bound) (n := n) (J := J) (xi := xi)
          (epsilon := epsilon) (P := P) (threshold := threshold)
          (base := base) (Kcut := Kcut) (Rtrace := Rtrace)
          (Rroom := Rroom) (start := start) (i := i) st sandwich hω
          htrace_le hi hroom_iter hroom_depth hscale hlow hcover hfacts
          (haccept i hi st htrace_le))

/--
Room-depth split fixed-carrier bounded trace wrapper with transition-shaped
acceptance.

Compared with `_roomDepth`, the remaining acceptance premise is narrowed to
the exact stopping transition selected by the source first-hit packet at each
reached state.
-/
theorem taoSection7Case3_boundedLocalUsedTrace_of_baseKcutRange_notEStar_sandwich_roomDepth_accept
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace Rroom start : ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (h0 : st0.q ≤ start)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
        bound)
    (hω : ω ∉ EStarUsed)
    (hroom_iter :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold Rroom start P)
    (hroom_depth : Rtrace + 1 ≤ Rroom)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (haccept_step :
      ∀ i : ℕ, i < Rtrace →
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family (pointAtΩ ω) bound n J xi epsilon P threshold
            (taoSection7Case3ExitGapBoundWithBase base Kcut),
        st.q ≤
            ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i])
              start →
        ∀ {first : ℕ} {Γ : TaoSection7Triangle},
          first < P →
          TaoSection7Case3StoppingTransition
            (pointAtΩ ω) family st.q st.old first Γ →
          taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
          Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts)
        (used :=
          {p : ℕ |
            p ∈ Finset.range
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
                start + 1)})
        (allowedFin :=
          Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1))
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) := by
  exact
    taoSection7Case3_boundedLocalUsedTrace_of_statefulStep
      (W := W) (family := family) (pointAt := pointAtΩ ω)
      (Accepts := Accepts)
      (used :=
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)})
      (allowedFin :=
        Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
      (bound := bound) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (base := base) (Kcut := Kcut) (R := Rtrace) (start := start)
      st0 h0
      (fun i hi st htrace_le =>
        taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_baseKcutRange_notEStar_sandwich_roomDepth_accept
          (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
          (Accepts := Accepts) (EStarUsed := EStarUsed)
          (bound := bound) (n := n) (J := J) (xi := xi)
          (epsilon := epsilon) (P := P) (threshold := threshold)
          (base := base) (Kcut := Kcut) (Rtrace := Rtrace)
          (Rroom := Rroom) (start := start) (i := i) st sandwich hω
          htrace_le hi hroom_iter hroom_depth hscale hlow hcover hfacts
          (haccept_step i hi st htrace_le))

/--
Global transition-acceptance wrapper for the room-depth bounded trace.

This is a transport layer over `_roomDepth_accept`: callers may provide one
finite-window, transition-shaped acceptance compatibility premise for the
whole sample, rather than an indexed per-state callback.
-/
theorem taoSection7Case3_boundedLocalUsedTrace_of_baseKcutRange_notEStar_sandwich_roomDepth_transitionAccept
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace Rroom start : ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (h0 : st0.q ≤ start)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
        bound)
    (hω : ω ∉ EStarUsed)
    (hroom_iter :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold Rroom start P)
    (hroom_depth : Rtrace + 1 ≤ Rroom)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (haccept_transition :
      ∀ {q first : ℕ} {old Γ : TaoSection7Triangle},
        first < P →
        TaoSection7Case3StoppingTransition (pointAtΩ ω) family q old first Γ →
        taoSection7SourceBlackInDomain n xi epsilon J ((pointAtΩ ω) first) →
        Accepts q old first Γ) :
    Nonempty
      (TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts)
        (used :=
          {p : ℕ |
            p ∈ Finset.range
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
                start + 1)})
        (allowedFin :=
          Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1))
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) :=
  taoSection7Case3_boundedLocalUsedTrace_of_baseKcutRange_notEStar_sandwich_roomDepth_accept
    (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
    (Accepts := Accepts) (EStarUsed := EStarUsed) (bound := bound)
    (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
    (threshold := threshold) (base := base) (Kcut := Kcut)
    (Rtrace := Rtrace) (Rroom := Rroom) (start := start) st0 h0
    sandwich hω hroom_iter hroom_depth hscale hlow hcover hfacts
    (fun _i _hi st _htrace_le {first} {Γ} hfirst_lt hstep hblack =>
      haccept_transition (q := st.q) (first := first) (old := st.old)
        (Γ := Γ) hfirst_lt hstep hblack)

/--
Room-depth split fixed-carrier bounded trace wrapper with source-provenance
acceptance.

At each reached state, the acceptance callback consumes the selected first-hit
source packet before any transition-shaped erasure is needed by downstream
encounter data.
-/
theorem taoSection7Case3_boundedLocalUsedTrace_of_baseKcutRange_notEStar_sandwich_roomDepth_acceptSource
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAtΩ : Ω → ℕ → TaoSection7Point)
    {ω : Ω}
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {EStarUsed : Set Ω}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut Rtrace Rroom start : ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family (pointAtΩ ω) bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (h0 : st0.q ≤ start)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAtΩ family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
        bound)
    (hω : ω ∉ EStarUsed)
    (hroom_iter :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold Rroom start P)
    (hroom_depth : Rtrace + 1 ≤ Rroom)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W (pointAtΩ ω) n J xi epsilon P)
    (haccept_src :
      ∀ i : ℕ, i < Rtrace →
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family (pointAtΩ ω) bound n J xi epsilon P threshold
            (taoSection7Case3ExitGapBoundWithBase base Kcut),
        st.q ≤
            ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i])
              start →
        ∀ {candidate first : ℕ} {Γ : TaoSection7Triangle},
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family (pointAtΩ ω) st.j st.s st.pre st.pres P st.q st.old Γ
            candidate first →
          Accepts st.q st.old first Γ) :
    Nonempty
      (TaoSection7Case3BoundedLocalUsedTrace
        (W := W) (family := family) (pointAt := pointAtΩ ω)
        (Accepts := Accepts)
        (used :=
          {p : ℕ |
            p ∈ Finset.range
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
                start + 1)})
        (allowedFin :=
          Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1))
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (R := Rtrace) (start := start) st0) := by
  exact
    taoSection7Case3_boundedLocalUsedTrace_of_statefulStep
      (W := W) (family := family) (pointAt := pointAtΩ ω)
      (Accepts := Accepts)
      (used :=
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)})
      (allowedFin :=
        Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
      (bound := bound) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (base := base) (Kcut := Kcut) (R := Rtrace) (start := start)
      st0 h0
      (fun i hi st htrace_le =>
        taoSection7Case3_exists_chosenActiveLocalUsedStepWithGap_of_baseKcutRange_notEStar_sandwich_roomDepth_acceptSource
          (W := W) (pointAtΩ := pointAtΩ) (ω := ω) (family := family)
          (Accepts := Accepts) (EStarUsed := EStarUsed)
          (bound := bound) (n := n) (J := J) (xi := xi)
          (epsilon := epsilon) (P := P) (threshold := threshold)
          (base := base) (Kcut := Kcut) (Rtrace := Rtrace)
          (Rroom := Rroom) (start := start) (i := i) st sandwich hω
          htrace_le hi hroom_iter hroom_depth hscale hlow hcover hfacts
          (haccept_src i hi st htrace_le))

/--
Branch-local low-white subset bridge whose bounded trace is produced from the
fixed base-Kcut source carrier.

This composes the room-depth transition-acceptance trace producer with the
branch-local bounded-trace low-white endpoint consumer.  Trace production is
only requested for samples that are already in the low-white event and outside
the two exceptional events.
-/
theorem taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_baseKcutRange_notEStar_sandwich_roomDepth_transitionAccept_onLowWhite
    {Ω : Type*} [Fintype Ω]
    {sourceAt : Ω → ℕ → TaoSection7Point}
    {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {Accepts : Ω → ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {family : Set TaoSection7Triangle}
    {bound : ℕ → ℝ}
    {n J P threshold base Kcut Rtrace Rroom start : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count : Ω → ℕ}
    {st0 :
      ∀ ω : Ω,
        TaoSection7Case3ActiveSourceStateWithGap
          (W ω) family (pointAt ω) bound n J xi epsilon P threshold
          (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    {EStarUsed FSlack : Set Ω}
    (hidentity :
      ∀ ω : Ω,
        TaoSection7Case3ActualRunSourceIdentity
          (sourceAt ω) (restart ω) (W ω)
          (taoSection7SourceBlackInDomain n xi epsilon J)
          (pointAt ω) family n J xi epsilon P (steps ω)
          (Rtrace + 1) (tR ω) (lemma79Count ω))
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          TaoSection7Case3InitialStoppingStep
            (pointAt ω) family (st0 ω).q (st0 ω).old)
    (hfirst0_ltP :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack → (st0 ω).q < P)
    (h0 :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack → (st0 ω).q ≤ start)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAt family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
        bound)
    (hroom_iter :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold Rroom start P)
    (hroom_depth : Rtrace + 1 ≤ Rroom)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfacts :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          TaoSection7Case3AllWindowSourceFacts
            (W ω) (pointAt ω) n J xi epsilon P)
    (haccept_transition :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
        ∀ {q first : ℕ} {old Γ : TaoSection7Triangle},
          first < P →
          TaoSection7Case3StoppingTransition (pointAt ω) family q old first Γ →
          taoSection7SourceBlackInDomain n xi epsilon J ((pointAt ω) first) →
          Accepts ω q old first Γ)
    (hmany :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          threshold < lemma79Count ω) :
    taoSection7Case3LowWhiteEvent W P threshold ⊆ EStarUsed ∪ FSlack := by
  refine
    taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_boundedLocalUsedTrace_onLowWhite
      (Accepts := Accepts)
      (used := fun _ω : Ω =>
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)})
      (allowedFin := fun _ω : Ω =>
        Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
      (bound := fun _ω : Ω => bound)
      (Rtail := Rtrace) (start := start) (st0 := st0)
      (hidentity := hidentity) (hpair := hpair) (hinit := hinit)
      (hfirst0_ltP := hfirst0_ltP) ?_ (hmany := hmany)
  intro ω hlow hnotE hnotF
  have hlow_count : taoSection7Case3WindowWhiteCount (W ω) P ≤ threshold := by
    simpa [taoSection7Case3LowWhiteEvent, taoSection7Case3LowWhite] using
      hlow
  exact
    Classical.choice
      (taoSection7Case3_boundedLocalUsedTrace_of_baseKcutRange_notEStar_sandwich_roomDepth_transitionAccept
        (W := W ω) (pointAtΩ := pointAt) (ω := ω) (family := family)
        (Accepts := Accepts ω) (EStarUsed := EStarUsed)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (Rtrace := Rtrace)
        (Rroom := Rroom) (start := start) (st0 ω)
        (h0 ω hlow hnotE hnotF) sandwich hnotE hroom_iter hroom_depth
        hscale hlow_count hcover (hfacts ω hlow hnotE hnotF)
        (fun {q} {first} {old} {Γ} hfirst_lt hstep hblack =>
          haccept_transition ω hlow hnotE hnotF (q := q) (first := first)
            (old := old) (Γ := Γ) hfirst_lt hstep hblack))

/--
Branch-local low-white subset bridge with source-provenance-shaped acceptance.

This is the branch-local endpoint composer over the room-depth source
acceptance trace producer.  Acceptance is only requested after fixing a
low-white sample outside `E*_used` and `F*`.
-/
theorem taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_baseKcutRange_notEStar_sandwich_roomDepth_acceptSource_onLowWhite
    {Ω : Type*} [Fintype Ω]
    {sourceAt : Ω → ℕ → TaoSection7Point}
    {restart : Ω → ℕ}
    {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {Accepts : Ω → ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {family : Set TaoSection7Triangle}
    {bound : ℕ → ℝ}
    {n J P threshold base Kcut Rtrace Rroom start : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {steps : Ω → List (ℕ × TaoSection7Triangle)}
    {tR lemma79Count : Ω → ℕ}
    {st0 :
      ∀ ω : Ω,
        TaoSection7Case3ActiveSourceStateWithGap
          (W ω) family (pointAt ω) bound n J xi epsilon P threshold
          (taoSection7Case3ExitGapBoundWithBase base Kcut)}
    {EStarUsed FSlack : Set Ω}
    (hidentity :
      ∀ ω : Ω,
        TaoSection7Case3ActualRunSourceIdentity
          (sourceAt ω) (restart ω) (W ω)
          (taoSection7SourceBlackInDomain n xi epsilon J)
          (pointAt ω) family n J xi epsilon P (steps ω)
          (Rtrace + 1) (tR ω) (lemma79Count ω))
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hinit :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          TaoSection7Case3InitialStoppingStep
            (pointAt ω) family (st0 ω).q (st0 ω).old)
    (hfirst0_ltP :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack → (st0 ω).q < P)
    (h0 :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack → (st0 ω).q ≤ start)
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAt family EStarUsed
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)}
        (Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
        bound)
    (hroom_iter :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold Rroom start P)
    (hroom_depth : Rtrace + 1 ≤ Rroom)
    (hscale :
      TaoSection7Case3RecurrenceScale bound
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hfacts :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          TaoSection7Case3AllWindowSourceFacts
            (W ω) (pointAt ω) n J xi epsilon P)
    (haccept_src :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
        ∀ {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
          {q candidate first : ℕ} {old Γ : TaoSection7Triangle},
          TaoSection7Case3FirstHitSourceProvenance
            (taoSection7SourceBlackInDomain n xi epsilon J)
            family (pointAt ω) j s pre pres P q old Γ candidate first →
          Accepts ω q old first Γ)
    (hmany :
      ∀ ω : Ω, ω ∈ taoSection7Case3LowWhiteEvent W P threshold →
        ω ∉ EStarUsed → ω ∉ FSlack →
          threshold < lemma79Count ω) :
    taoSection7Case3LowWhiteEvent W P threshold ⊆ EStarUsed ∪ FSlack := by
  refine
    taoSection7Case3_lowWhiteEvent_subset_EStarUsed_union_FSlack_of_actualRunSourceIdentity_boundedLocalUsedTrace_onLowWhite
      (Accepts := Accepts)
      (used := fun _ω : Ω =>
        {p : ℕ |
          p ∈ Finset.range
            (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
              start + 1)})
      (allowedFin := fun _ω : Ω =>
        Finset.range
          (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[Rtrace])
            start + 1))
      (bound := fun _ω : Ω => bound)
      (Rtail := Rtrace) (start := start) (st0 := st0)
      (hidentity := hidentity) (hpair := hpair) (hinit := hinit)
      (hfirst0_ltP := hfirst0_ltP) ?_ (hmany := hmany)
  intro ω hlow hnotE hnotF
  have hlow_count : taoSection7Case3WindowWhiteCount (W ω) P ≤ threshold := by
    simpa [taoSection7Case3LowWhiteEvent, taoSection7Case3LowWhite] using
      hlow
  exact
    Classical.choice
      (taoSection7Case3_boundedLocalUsedTrace_of_baseKcutRange_notEStar_sandwich_roomDepth_acceptSource
        (W := W ω) (pointAtΩ := pointAt) (ω := ω) (family := family)
        (Accepts := Accepts ω) (EStarUsed := EStarUsed)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (base := base) (Kcut := Kcut) (Rtrace := Rtrace)
        (Rroom := Rroom) (start := start) (st0 ω)
        (h0 ω hlow hnotE hnotF) sandwich hnotE hroom_iter hroom_depth
        hscale hlow_count hcover (hfacts ω hlow hnotE hnotF)
        (fun _i _hi st _htrace_le {candidate} {first} {Γ} hsrc =>
          haccept_src ω hlow hnotE hnotF
            (j := st.j) (s := st.s) (pre := st.pre) (pres := st.pres)
            (q := st.q) (candidate := candidate) (first := first)
            (old := st.old) (Γ := Γ) hsrc))

namespace TaoSection7Case3ActiveSourceStateWithGap

def seq
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound)
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold gapBound,
          TaoSection7Case3ChosenActiveStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (bound := bound) (n := n) (J := J)
            (xi := xi) (epsilon := epsilon) (P := P)
            (threshold := threshold) (gapBound := gapBound) st) :
    ℕ →
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound :=
  fun i =>
    Nat.rec st0
      (fun i st =>
        TaoSection7Case3ChosenActiveStepWithGap.nextState
          (advance i st)) i

def seqUsed
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound)
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold gapBound,
          TaoSection7Case3ChosenActiveUsedStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := gapBound) st) :
    ℕ →
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound :=
  TaoSection7Case3ActiveSourceStateWithGap.seq
    (W := W) (family := family) (pointAt := pointAt)
    (Accepts := Accepts) (bound := bound) (n := n) (J := J)
    (xi := xi) (epsilon := epsilon) (P := P)
    (threshold := threshold) (gapBound := gapBound) st0
    (fun i st => (advance i st).step)

def seqLocalUsed
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (localAllowed :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound →
        Set ℕ)
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound)
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold gapBound,
          TaoSection7Case3ChosenActiveLocalUsedStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (localAllowed := localAllowed st)
            (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := gapBound) st) :
    ℕ →
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound :=
  TaoSection7Case3ActiveSourceStateWithGap.seqUsed
    (W := W) (family := family) (pointAt := pointAt)
    (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
    (bound := bound) (n := n) (J := J) (xi := xi)
    (epsilon := epsilon) (P := P) (threshold := threshold)
    (gapBound := gapBound) st0
    (fun i st => (advance i st).usedStep)

end TaoSection7Case3ActiveSourceStateWithGap

namespace TaoSection7Case3ActiveSourceTraceWithGap

def t
    {W : ℕ → Prop} {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point} {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (trace :
      ℕ →
        TaoSection7Case3ActiveSourceStateWithGap
          W family pointAt bound n J xi epsilon P threshold gapBound) :
    ℕ → ℕ :=
  fun i => (trace i).q

def tri
    {W : ℕ → Prop} {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point} {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (trace :
      ℕ →
        TaoSection7Case3ActiveSourceStateWithGap
          W family pointAt bound n J xi epsilon P threshold gapBound) :
    ℕ → TaoSection7Triangle :=
  fun i => (trace i).old

def j
    {W : ℕ → Prop} {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point} {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (trace :
      ℕ →
        TaoSection7Case3ActiveSourceStateWithGap
          W family pointAt bound n J xi epsilon P threshold gapBound) :
    ℕ → ℕ+ :=
  fun i => (trace i).j

def s
    {W : ℕ → Prop} {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point} {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (trace :
      ℕ →
        TaoSection7Case3ActiveSourceStateWithGap
          W family pointAt bound n J xi epsilon P threshold gapBound) :
    ℕ → ℕ :=
  fun i => (trace i).s

def pre
    {W : ℕ → Prop} {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point} {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (trace :
      ℕ →
        TaoSection7Case3ActiveSourceStateWithGap
          W family pointAt bound n J xi epsilon P threshold gapBound) :
    ℕ → List ℕ :=
  fun i => (trace i).pre

def pres
    {W : ℕ → Prop} {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point} {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (trace :
      ℕ →
        TaoSection7Case3ActiveSourceStateWithGap
          W family pointAt bound n J xi epsilon P threshold gapBound) :
    ℕ → List (List ℕ) :=
  fun i => (trace i).pres

def selectedStopsFinset
    {W : ℕ → Prop} {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point} {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (trace :
      ℕ →
        TaoSection7Case3ActiveSourceStateWithGap
          W family pointAt bound n J xi epsilon P threshold gapBound)
    (R : ℕ) : Finset ℕ :=
  (Finset.range R).image
    (fun i => TaoSection7Case3ActiveSourceTraceWithGap.t trace (i + 1))

end TaoSection7Case3ActiveSourceTraceWithGap

theorem taoSection7Case3_activeSourceTraceWithGap_t_succ_mem_used_of_seqUsed
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound)
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold gapBound,
          TaoSection7Case3ChosenActiveUsedStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := gapBound) st)
    (i : ℕ) :
    let trace :=
      TaoSection7Case3ActiveSourceStateWithGap.seqUsed
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st0 advance
    TaoSection7Case3ActiveSourceTraceWithGap.t trace (i + 1) ∈ used := by
  simpa [TaoSection7Case3ActiveSourceTraceWithGap.t,
    TaoSection7Case3ActiveSourceStateWithGap.seqUsed,
    TaoSection7Case3ActiveSourceStateWithGap.seq,
    TaoSection7Case3ChosenActiveStepWithGap.nextState]
    using
      (advance i
        (TaoSection7Case3ActiveSourceStateWithGap.seqUsed
          (W := W) (family := family) (pointAt := pointAt)
          (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
          (bound := bound) (n := n) (J := J) (xi := xi)
          (epsilon := epsilon) (P := P) (threshold := threshold)
          (gapBound := gapBound) st0 advance i)).first_mem_used

theorem taoSection7Case3_activeSourceTraceWithGap_t_succ_mem_allowedFin_of_seqUsed
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound)
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold gapBound,
          TaoSection7Case3ChosenActiveUsedStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := gapBound) st)
    (i : ℕ) :
    let trace :=
      TaoSection7Case3ActiveSourceStateWithGap.seqUsed
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) st0 advance
    TaoSection7Case3ActiveSourceTraceWithGap.t trace (i + 1) ∈ allowedFin := by
  simpa [TaoSection7Case3ActiveSourceTraceWithGap.t,
    TaoSection7Case3ActiveSourceStateWithGap.seqUsed,
    TaoSection7Case3ActiveSourceStateWithGap.seq,
    TaoSection7Case3ChosenActiveStepWithGap.nextState]
    using
      (advance i
        (TaoSection7Case3ActiveSourceStateWithGap.seqUsed
          (W := W) (family := family) (pointAt := pointAt)
          (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
          (bound := bound) (n := n) (J := J) (xi := xi)
          (epsilon := epsilon) (P := P) (threshold := threshold)
          (gapBound := gapBound) st0 advance i)).first_mem_allowedFin

theorem taoSection7Case3_selectedStopsFinset_mem_used_of_seqUsed
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound)
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold gapBound,
          TaoSection7Case3ChosenActiveUsedStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := gapBound) st)
    (R p : ℕ) :
    p ∈
        TaoSection7Case3ActiveSourceTraceWithGap.selectedStopsFinset
          (TaoSection7Case3ActiveSourceStateWithGap.seqUsed
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := gapBound) st0 advance) R →
      p ∈ used := by
  intro hp
  rcases Finset.mem_image.mp hp with ⟨i, _hi, rfl⟩
  exact
    taoSection7Case3_activeSourceTraceWithGap_t_succ_mem_used_of_seqUsed
      (W := W) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
      (bound := bound) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := gapBound) st0 advance i

theorem taoSection7Case3_selectedStopsFinset_subset_allowedFin_of_seqUsed
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound)
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold gapBound,
          TaoSection7Case3ChosenActiveUsedStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := gapBound) st)
    (R : ℕ) :
    TaoSection7Case3ActiveSourceTraceWithGap.selectedStopsFinset
        (TaoSection7Case3ActiveSourceStateWithGap.seqUsed
          (W := W) (family := family) (pointAt := pointAt)
          (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
          (bound := bound) (n := n) (J := J) (xi := xi)
          (epsilon := epsilon) (P := P) (threshold := threshold)
          (gapBound := gapBound) st0 advance) R ⊆
      allowedFin := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨i, _hi, rfl⟩
  exact
    taoSection7Case3_activeSourceTraceWithGap_t_succ_mem_allowedFin_of_seqUsed
      (W := W) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
      (bound := bound) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := gapBound) st0 advance i

theorem taoSection7Case3_activeSourceTraceWithGap_t_succ_le_baseKcutNextBound_of_seqLocalUsed
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut : ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold
            (taoSection7Case3ExitGapBoundWithBase base Kcut),
          TaoSection7Case3ChosenActiveLocalUsedStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts)
            (localAllowed :=
              taoSection7Case3LocalSelectedEnvelope
                (taoSection7Case3ExitGapBoundWithBase base Kcut)
                threshold st.q)
            (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st)
    (i : ℕ) :
    let trace :=
      TaoSection7Case3ActiveSourceStateWithGap.seqLocalUsed
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
        (fun st =>
          taoSection7Case3LocalSelectedEnvelope
            (taoSection7Case3ExitGapBoundWithBase base Kcut)
            threshold st.q)
        st0 advance
    TaoSection7Case3ActiveSourceTraceWithGap.t trace (i + 1) ≤
      taoSection7Case3BaseKcutNextBound base Kcut threshold
        (TaoSection7Case3ActiveSourceTraceWithGap.t trace i) := by
  simpa [TaoSection7Case3ActiveSourceTraceWithGap.t,
    TaoSection7Case3ActiveSourceStateWithGap.seqLocalUsed,
    TaoSection7Case3ActiveSourceStateWithGap.seqUsed,
    TaoSection7Case3ActiveSourceStateWithGap.seq,
    TaoSection7Case3ChosenActiveStepWithGap.nextState]
    using
      (TaoSection7Case3ChosenActiveLocalUsedStepWithGap.first_le_baseKcutNextBound
        (base := base) (Kcut := Kcut)
        (hstep :=
          advance i
            (TaoSection7Case3ActiveSourceStateWithGap.seqLocalUsed
              (W := W) (family := family) (pointAt := pointAt)
              (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
              (bound := bound) (n := n) (J := J) (xi := xi)
              (epsilon := epsilon) (P := P) (threshold := threshold)
              (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
              (fun st =>
                taoSection7Case3LocalSelectedEnvelope
                  (taoSection7Case3ExitGapBoundWithBase base Kcut)
                  threshold st.q)
              st0 advance i)))

theorem taoSection7Case3_activeSourceTraceWithGap_t_le_baseKcut_iterate_of_seqLocalUsed
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {used : Set ℕ} {allowedFin : Finset ℕ}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold base Kcut start : ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold
        (taoSection7Case3ExitGapBoundWithBase base Kcut))
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold
            (taoSection7Case3ExitGapBoundWithBase base Kcut),
          TaoSection7Case3ChosenActiveLocalUsedStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts)
            (localAllowed :=
              taoSection7Case3LocalSelectedEnvelope
                (taoSection7Case3ExitGapBoundWithBase base Kcut)
                threshold st.q)
            (used := used) (allowedFin := allowedFin)
            (bound := bound) (n := n) (J := J) (xi := xi)
            (epsilon := epsilon) (P := P) (threshold := threshold)
            (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut) st)
    (h0 : st0.q ≤ start)
    (i : ℕ) :
    let trace :=
      TaoSection7Case3ActiveSourceStateWithGap.seqLocalUsed
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
        (bound := bound) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
        (fun st =>
          taoSection7Case3LocalSelectedEnvelope
            (taoSection7Case3ExitGapBoundWithBase base Kcut)
            threshold st.q)
        st0 advance
    TaoSection7Case3ActiveSourceTraceWithGap.t trace i ≤
      ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i]) start := by
  induction i with
  | zero =>
      simpa [TaoSection7Case3ActiveSourceTraceWithGap.t,
        TaoSection7Case3ActiveSourceStateWithGap.seqLocalUsed,
        TaoSection7Case3ActiveSourceStateWithGap.seqUsed,
        TaoSection7Case3ActiveSourceStateWithGap.seq] using h0
  | succ i ih =>
      have hstep :
          let trace :=
            TaoSection7Case3ActiveSourceStateWithGap.seqLocalUsed
              (W := W) (family := family) (pointAt := pointAt)
              (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
              (bound := bound) (n := n) (J := J) (xi := xi)
              (epsilon := epsilon) (P := P) (threshold := threshold)
              (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
              (fun st =>
                taoSection7Case3LocalSelectedEnvelope
                  (taoSection7Case3ExitGapBoundWithBase base Kcut)
                  threshold st.q)
              st0 advance
          TaoSection7Case3ActiveSourceTraceWithGap.t trace (i + 1) ≤
            taoSection7Case3BaseKcutNextBound base Kcut threshold
              (TaoSection7Case3ActiveSourceTraceWithGap.t trace i) :=
        taoSection7Case3_activeSourceTraceWithGap_t_succ_le_baseKcutNextBound_of_seqLocalUsed
          (W := W) (family := family) (pointAt := pointAt)
          (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
          (bound := bound) (n := n) (J := J) (xi := xi)
          (epsilon := epsilon) (P := P) (threshold := threshold)
          (base := base) (Kcut := Kcut) st0 advance i
      have hmono :
          taoSection7Case3BaseKcutNextBound base Kcut threshold
              (TaoSection7Case3ActiveSourceTraceWithGap.t
                (TaoSection7Case3ActiveSourceStateWithGap.seqLocalUsed
                  (W := W) (family := family) (pointAt := pointAt)
                  (Accepts := Accepts) (used := used) (allowedFin := allowedFin)
                  (bound := bound) (n := n) (J := J) (xi := xi)
                  (epsilon := epsilon) (P := P) (threshold := threshold)
                  (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
                  (fun st =>
                    taoSection7Case3LocalSelectedEnvelope
                      (taoSection7Case3ExitGapBoundWithBase base Kcut)
                      threshold st.q)
                  st0 advance) i) ≤
            taoSection7Case3BaseKcutNextBound base Kcut threshold
              (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i]) start) :=
        taoSection7Case3BaseKcutNextBound_mono base Kcut threshold ih
      exact le_trans hstep (by
        simpa [Function.iterate_succ_apply'] using hmono)

def taoSection7Case3_indexedRebasedSourceUpdateWithGap_of_activeSourceStateTrace_step
    {W : ℕ → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {bound : ℕ → ℝ}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    (st0 :
      TaoSection7Case3ActiveSourceStateWithGap
        W family pointAt bound n J xi epsilon P threshold gapBound)
    (advance :
      ∀ _i : ℕ,
        ∀ st :
          TaoSection7Case3ActiveSourceStateWithGap
            W family pointAt bound n J xi epsilon P threshold gapBound,
          TaoSection7Case3ChosenActiveStepWithGap
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (bound := bound) (n := n) (J := J)
            (xi := xi) (epsilon := epsilon) (P := P)
            (threshold := threshold) (gapBound := gapBound) st)
    (i : ℕ) :
    let trace :=
      TaoSection7Case3ActiveSourceStateWithGap.seq
        (W := W) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (bound := bound) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (gapBound := gapBound) st0 advance
    TaoSection7Case3IndexedRebasedSourceUpdateWithGap
      (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
      (family := family) (pointAt := pointAt) (Accepts := Accepts)
      (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
      (threshold := threshold) (gapBound := gapBound)
      (TaoSection7Case3ActiveSourceTraceWithGap.t trace)
      (TaoSection7Case3ActiveSourceTraceWithGap.tri trace)
      (TaoSection7Case3ActiveSourceTraceWithGap.j trace)
      (TaoSection7Case3ActiveSourceTraceWithGap.s trace)
      (TaoSection7Case3ActiveSourceTraceWithGap.pre trace)
      (TaoSection7Case3ActiveSourceTraceWithGap.pres trace) i := by
  dsimp only
  exact
    TaoSection7Case3OneStepRebasedSourceUpdateWithGap.to_indexedRebasedSourceUpdateWithGap
      (hupdate :=
        (advance i
          (TaoSection7Case3ActiveSourceStateWithGap.seq
            (W := W) (family := family) (pointAt := pointAt)
            (Accepts := Accepts) (bound := bound) (n := n) (J := J)
            (xi := xi) (epsilon := epsilon) (P := P)
            (threshold := threshold) (gapBound := gapBound)
            st0 advance i)).update)
      (by
        simp [TaoSection7Case3ActiveSourceTraceWithGap.t,
          TaoSection7Case3ActiveSourceStateWithGap.seq,
          TaoSection7Case3ChosenActiveStepWithGap.nextState])
      (by
        simp [TaoSection7Case3ActiveSourceTraceWithGap.tri,
          TaoSection7Case3ActiveSourceStateWithGap.seq,
          TaoSection7Case3ChosenActiveStepWithGap.nextState])
      (by
        simp [TaoSection7Case3ActiveSourceTraceWithGap.j,
          TaoSection7Case3ActiveSourceTraceWithGap.pre,
          TaoSection7Case3ActiveSourceStateWithGap.seq,
          TaoSection7Case3ChosenActiveStepWithGap.nextState])
      (by
        simp [TaoSection7Case3ActiveSourceTraceWithGap.s,
          TaoSection7Case3ActiveSourceTraceWithGap.pre,
          TaoSection7Case3ActiveSourceStateWithGap.seq,
          TaoSection7Case3ChosenActiveStepWithGap.nextState])
      (by
        simp [TaoSection7Case3ActiveSourceTraceWithGap.pre,
          TaoSection7Case3ActiveSourceStateWithGap.seq,
          TaoSection7Case3ChosenActiveStepWithGap.nextState])
      (by
        simp [TaoSection7Case3ActiveSourceTraceWithGap.pres,
          TaoSection7Case3ActiveSourceStateWithGap.seq,
          TaoSection7Case3ChosenActiveStepWithGap.nextState])

/--
Active-state version of the existential one-step packet producer.

It keeps the chosen split/source packet while adding the successor active
triangle and start-budget facts needed by the iterative route.
-/
theorem taoSection7Case3_exists_oneStepActiveRebasedSourceUpdateWithGap_of_fullWindowSourcePathDataWithGap
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {family : Set TaoSection7Triangle}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {bound : ℕ → ℝ} {gapBound B : ℕ → ℕ}
    {allowed : Set ℕ}
    {P start threshold q : ℕ}
    {j : ℕ+} {s : ℕ} {pre : List ℕ} {pres : List (List ℕ)}
    {old : TaoSection7Triangle}
    (hq : q ∈ Finset.Icc start (start + threshold))
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold q gapBound j s pre pres)
    (hscale : TaoSection7Case3RecurrenceScale bound gapBound)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hactive :
      TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old)
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hroom_next :
      ∀ first : ℕ, q < first → first < P →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold) P first)
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (hright :
      taoSection7Case3LaterSearchBound gapBound threshold
          (start + threshold) ≤ B start)
    (hallowed_first :
      ∀ first : ℕ, q < first → first < P → first ∈ allowed)
    (hnotLarge :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound)
    (haccept :
      ∀ first Γ,
        first < P →
        taoSection7SourceBlackInDomain n xi epsilon J (pointAt first) →
        TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first →
        Γ ∈ family →
        Γ.Mem (pointAt first) →
        Γ ≠ old →
        Accepts q old first Γ) :
    ∃ hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := q) (gapBound := gapBound)
        j s pre pres old,
      hupdate.first ≤ B start ∧
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold)
          P hupdate.first ∧
        TaoSection7Case3ActiveTriangleAtWithBound
          family pointAt bound hupdate.first hupdate.triangle := by
  rcases
      taoSection7Case3_exists_encounterStep_rebasedWithGap_and_budget_of_fullWindowSourcePathDataWithGap
        (W := W) (pointAt := pointAt) (family := family)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (bound := bound) (gapBound := gapBound)
        (B := B) (P := P) (start := start) (threshold := threshold)
        (q := q) (j := j) (s := s) (pre := pre) (pres := pres)
        (old := old) hq hfull hscale hlow hroom hactive hcover
        hroom_next hfacts hright haccept with
    ⟨candidate, first, Γ, before, next, after, hsplit, hidx, hsrc,
      hstep, hrebase, hbudget⟩
  have hroom_first :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P first :=
    hroom_next first hsrc.first_hit.1 hsrc.first_ltP
  have hallowed : first ∈ allowed :=
    hallowed_first first hsrc.first_hit.1 hsrc.first_ltP
  have hsmall : Γ.size < bound first :=
    taoSection7Case3_triangle_size_lt_of_not_large_union
      (pointAt := pointAt) (family := family) (allowed := allowed)
      (bound := bound) hnotLarge hallowed hsrc.new_mem_family hsrc.new_mem
  let hupdate :
      TaoSection7Case3OneStepRebasedSourceUpdateWithGap
        (W := W) (black := taoSection7SourceBlackInDomain n xi epsilon J)
        (family := family) (pointAt := pointAt) (Accepts := Accepts)
        (n := n) (J := J) (xi := xi) (epsilon := epsilon) (P := P)
        (threshold := threshold) (q := q) (gapBound := gapBound)
        j s pre pres old :=
    { candidate := candidate
      first := first
      triangle := Γ
      before := before
      next := next
      after := after
      split := hsplit
      index := hidx
      source := hsrc
      encounter := hstep
      rebased := hrebase }
  refine ⟨hupdate, hbudget, hroom_first, ?_⟩
  exact
    { old_mem_family := hsrc.new_mem_family
      pivot_mem := hsrc.new_mem
      small_size := hsmall }

/--
Stateful recursor for indexed rebased source updates.

This packages the induction that propagates the `WithGap` full-window state
while constructing each indexed update from a local step.  The local step sees
the current state, so callers do not need to supply a separate all-index
`hfull` oracle.
-/
def taoSection7Case3_indexedRebasedSourceUpdatesWithGap_and_stateInvariant_of_statefulStep
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ} {gapBound : ℕ → ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (hstate0 :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold (t 0) gapBound
        (j 0) (s 0) (pre 0) (pres 0))
    (hstep :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i) →
        TaoSection7Case3IndexedRebasedSourceUpdateWithGap
          (W := W) (black := black) (family := family)
          (pointAt := pointAt) (Accepts := Accepts) (n := n)
          (J := J) (xi := xi) (epsilon := epsilon) (P := P)
          (threshold := threshold) (gapBound := gapBound)
          t tri j s pre pres i) :
    { _updates : ∀ i : ℕ, i < Rtail →
        TaoSection7Case3IndexedRebasedSourceUpdateWithGap
          (W := W) (black := black) (family := family)
          (pointAt := pointAt) (Accepts := Accepts) (n := n)
          (J := J) (xi := xi) (epsilon := epsilon) (P := P)
          (threshold := threshold) (gapBound := gapBound)
          t tri j s pre pres i //
      ∀ i : ℕ, i ≤ Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i) } := by
  induction Rtail with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro i hi
        omega
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        exact hstate0
  | succ Rtail ih =>
      let hrec :=
        ih (fun i hi hstate => hstep i (by omega) hstate)
      let hupdateRtail :=
        hstep Rtail (by omega) (hrec.2 Rtail (by omega))
      refine ⟨?_, ?_⟩
      · intro i hi
        by_cases hlt : i < Rtail
        · exact hrec.1 i hlt
        · have hi_eq : i = Rtail := by omega
          subst i
          exact hupdateRtail
      · intro i hi
        by_cases hle : i ≤ Rtail
        · exact hrec.2 i hle
        · have hi_eq : i = Rtail + 1 := by omega
          subst i
          exact hupdateRtail.to_sourceStateUpdate.2

theorem taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_statefulRebasedSourceUpdateStep
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ} {gapBound : ℕ → ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family (t 0) (tri 0))
    (hfirst_ltP : t 0 < P)
    (hstate0 :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold (t 0) gapBound
        (j 0) (s 0) (pre 0) (pres 0))
    (hstep :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i) →
        TaoSection7Case3IndexedRebasedSourceUpdateWithGap
          (W := W) (black := black) (family := family)
          (pointAt := pointAt) (Accepts := Accepts) (n := n)
          (J := J) (xi := xi) (epsilon := epsilon) (P := P)
          (threshold := threshold) (gapBound := gapBound)
          t tri j s pre pres i) :
    TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P (Rtail + 1) (t 0) (tri 0)
        (taoSection7Case3IndexedEncounterTail t tri 0 Rtail) ∧
      ∀ i : ℕ, i ≤ Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i) := by
  let hrec :=
    taoSection7Case3_indexedRebasedSourceUpdatesWithGap_and_stateInvariant_of_statefulStep
      (W := W) (black := black) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (Rtail := Rtail) (gapBound := gapBound) t tri j s pre pres
      hstate0 hstep
  constructor
  · exact
      taoSection7Case3_prefixRInputs_of_indexedEncounterTail
        (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (P := P) t tri
        (Rtail := Rtail) hinit hfirst_ltP
        (by
          intro i hi
          exact (hrec.1 i hi).encounter)
  · exact hrec.2

def taoSection7Case3_indexedRebasedSourceUpdateWithGap_of_firstHitSourceProvenance_split
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold : ℕ} {gapBound : ℕ → ℕ}
    {t : ℕ → ℕ} {tri : ℕ → TaoSection7Triangle}
    {j : ℕ → ℕ+} {s : ℕ → ℕ}
    {pre : ℕ → List ℕ} {pres : ℕ → List (List ℕ)}
    {i candidate : ℕ}
    {before : List (List ℕ)} {next : List ℕ}
    {after : List (List ℕ)}
    (hfull :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold (t i) gapBound
        (j i) (s i) (pre i) (pres i))
    (hsrc :
      TaoSection7Case3FirstHitSourceProvenance
        black family pointAt (j i) (s i) (pre i) (pres i)
        P (t i) (tri i) (tri (i + 1)) candidate (t (i + 1)))
    (hsplit : pres i = before ++ next :: after)
    (hidx : before.length + 1 = t (i + 1) - t i)
    (hroom_next :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P (t (i + 1)))
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (haccept : Accepts (t i) (tri i) (t (i + 1)) (tri (i + 1)))
    (hj_next :
      j (i + 1) =
        taoSection7SourceBlockStartJFrom (j i) (pre i :: before))
    (hs_next :
      s (i + 1) =
        taoSection7SourceBlockStartSFrom (s i) (pre i :: before))
    (hpre_next : pre (i + 1) = next)
    (hpres_next : pres (i + 1) = after) :
    TaoSection7Case3IndexedRebasedSourceUpdateWithGap
      (W := W) (black := black) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := gapBound) t tri j s pre pres i := by
  refine
    { before := before
      next := next
      after := after
      split := hsplit
      j_next := hj_next
      s_next := hs_next
      pre_next := hpre_next
      pres_next := hpres_next
      encounter := hsrc.to_encounterStep haccept
      rebased := ?_ }
  exact
    taoSection7Case3_fullWindowSourcePathDataWithGap_rebase_of_split
      (hfull := hfull) hsplit hidx hsrc.first_hit.1 hsrc.first_ltP
      (TaoSection7Case3AllWindowSourceFacts.white_iff_later_withGap
        hfacts hroom_next)
      (TaoSection7Case3AllWindowSourceFacts.domain_later_withGap
        hfacts hroom_next)

def taoSection7Case3_indexedRebasedSourceUpdatesWithGap_of_indexedFirstHitSourceProvenance_splits
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ} {gapBound : ℕ → ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (candidate : ℕ → ℕ)
    (before : ℕ → List (List ℕ)) (next : ℕ → List ℕ)
    (after : ℕ → List (List ℕ))
    (hfull :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i))
    (hsrc :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FirstHitSourceProvenance
          black family pointAt (j i) (s i) (pre i) (pres i)
          P (t i) (tri i) (tri (i + 1)) (candidate i) (t (i + 1)))
    (hsplit :
      ∀ i : ℕ, i < Rtail →
        pres i = before i ++ next i :: after i)
    (hidx :
      ∀ i : ℕ, i < Rtail →
        (before i).length + 1 = t (i + 1) - t i)
    (hroom_next :
      ∀ i : ℕ, i < Rtail →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold)
          P (t (i + 1)))
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (haccept :
      ∀ i : ℕ, i < Rtail →
        Accepts (t i) (tri i) (t (i + 1)) (tri (i + 1)))
    (hj_next :
      ∀ i : ℕ, i < Rtail →
        j (i + 1) =
          taoSection7SourceBlockStartJFrom (j i) (pre i :: before i))
    (hs_next :
      ∀ i : ℕ, i < Rtail →
        s (i + 1) =
          taoSection7SourceBlockStartSFrom (s i) (pre i :: before i))
    (hpre_next :
      ∀ i : ℕ, i < Rtail → pre (i + 1) = next i)
    (hpres_next :
      ∀ i : ℕ, i < Rtail → pres (i + 1) = after i) :
    ∀ i : ℕ, i < Rtail →
      TaoSection7Case3IndexedRebasedSourceUpdateWithGap
        (W := W) (black := black) (family := family) (pointAt := pointAt)
        (Accepts := Accepts) (n := n) (J := J) (xi := xi)
        (epsilon := epsilon) (P := P) (threshold := threshold)
        (gapBound := gapBound) t tri j s pre pres i := by
  intro i hi
  exact
    taoSection7Case3_indexedRebasedSourceUpdateWithGap_of_firstHitSourceProvenance_split
      (hfull := hfull i hi) (hsrc := hsrc i hi)
      (hsplit := hsplit i hi) (hidx := hidx i hi)
      (hroom_next := hroom_next i hi) (hfacts := hfacts)
      (haccept := haccept i hi) (hj_next := hj_next i hi)
      (hs_next := hs_next i hi) (hpre_next := hpre_next i hi)
      (hpres_next := hpres_next i hi)

theorem taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_statefulIndexedFirstHitSourceProvenance_splits
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ} {gapBound : ℕ → ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (candidate : ℕ → ℕ)
    (before : ℕ → List (List ℕ)) (next : ℕ → List ℕ)
    (after : ℕ → List (List ℕ))
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family (t 0) (tri 0))
    (hfirst_ltP : t 0 < P)
    (hstate0 :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold (t 0) gapBound
        (j 0) (s 0) (pre 0) (pres 0))
    (hsrc :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FirstHitSourceProvenance
          black family pointAt (j i) (s i) (pre i) (pres i)
          P (t i) (tri i) (tri (i + 1)) (candidate i) (t (i + 1)))
    (hsplit :
      ∀ i : ℕ, i < Rtail →
        pres i = before i ++ next i :: after i)
    (hidx :
      ∀ i : ℕ, i < Rtail →
        (before i).length + 1 = t (i + 1) - t i)
    (hroom_next :
      ∀ i : ℕ, i < Rtail →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold)
          P (t (i + 1)))
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (haccept :
      ∀ i : ℕ, i < Rtail →
        Accepts (t i) (tri i) (t (i + 1)) (tri (i + 1)))
    (hj_next :
      ∀ i : ℕ, i < Rtail →
        j (i + 1) =
          taoSection7SourceBlockStartJFrom (j i) (pre i :: before i))
    (hs_next :
      ∀ i : ℕ, i < Rtail →
        s (i + 1) =
          taoSection7SourceBlockStartSFrom (s i) (pre i :: before i))
    (hpre_next :
      ∀ i : ℕ, i < Rtail → pre (i + 1) = next i)
    (hpres_next :
      ∀ i : ℕ, i < Rtail → pres (i + 1) = after i) :
    TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P (Rtail + 1) (t 0) (tri 0)
        (taoSection7Case3IndexedEncounterTail t tri 0 Rtail) ∧
      ∀ i : ℕ, i ≤ Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i) := by
  exact
    taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_statefulRebasedSourceUpdateStep
      (black := black) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (Rtail := Rtail) (gapBound := gapBound) t tri j s pre pres
      hinit hfirst_ltP hstate0
      (by
        intro i hi hstate
        exact
          taoSection7Case3_indexedRebasedSourceUpdateWithGap_of_firstHitSourceProvenance_split
            (W := W) (black := black) (family := family)
            (pointAt := pointAt) (Accepts := Accepts) (n := n)
            (J := J) (xi := xi) (epsilon := epsilon) (P := P)
            (threshold := threshold) (gapBound := gapBound) (t := t)
            (tri := tri) (j := j) (s := s) (pre := pre)
            (pres := pres) (i := i) (candidate := candidate i)
            (before := before i) (next := next i) (after := after i)
            (hfull := hstate) (hsrc := hsrc i hi)
            (hsplit := hsplit i hi) (hidx := hidx i hi)
            (hroom_next := hroom_next i hi) (hfacts := hfacts)
            (haccept := haccept i hi) (hj_next := hj_next i hi)
            (hs_next := hs_next i hi) (hpre_next := hpre_next i hi)
            (hpres_next := hpres_next i hi))

theorem taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_indexedFirstHitSourceProvenance_splits
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ} {gapBound : ℕ → ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (candidate : ℕ → ℕ)
    (before : ℕ → List (List ℕ)) (next : ℕ → List ℕ)
    (after : ℕ → List (List ℕ))
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family (t 0) (tri 0))
    (hfirst_ltP : t 0 < P)
    (hstate0 :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold (t 0) gapBound
        (j 0) (s 0) (pre 0) (pres 0))
    (hfull :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i))
    (hsrc :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3FirstHitSourceProvenance
          black family pointAt (j i) (s i) (pre i) (pres i)
          P (t i) (tri i) (tri (i + 1)) (candidate i) (t (i + 1)))
    (hsplit :
      ∀ i : ℕ, i < Rtail →
        pres i = before i ++ next i :: after i)
    (hidx :
      ∀ i : ℕ, i < Rtail →
        (before i).length + 1 = t (i + 1) - t i)
    (hroom_next :
      ∀ i : ℕ, i < Rtail →
        taoSection7Case3ExitRoom
          (taoSection7Case3LaterSearchBound gapBound threshold)
          P (t (i + 1)))
    (hfacts :
      TaoSection7Case3AllWindowSourceFacts W pointAt n J xi epsilon P)
    (haccept :
      ∀ i : ℕ, i < Rtail →
        Accepts (t i) (tri i) (t (i + 1)) (tri (i + 1)))
    (hj_next :
      ∀ i : ℕ, i < Rtail →
        j (i + 1) =
          taoSection7SourceBlockStartJFrom (j i) (pre i :: before i))
    (hs_next :
      ∀ i : ℕ, i < Rtail →
        s (i + 1) =
          taoSection7SourceBlockStartSFrom (s i) (pre i :: before i))
    (hpre_next :
      ∀ i : ℕ, i < Rtail → pre (i + 1) = next i)
    (hpres_next :
      ∀ i : ℕ, i < Rtail → pres (i + 1) = after i) :
    TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P (Rtail + 1) (t 0) (tri 0)
        (taoSection7Case3IndexedEncounterTail t tri 0 Rtail) ∧
      ∀ i : ℕ, i ≤ Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i) := by
  exact
    taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_indexedSourceStateUpdates
      (black := black) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := gapBound) t tri j s pre pres hinit hfirst_ltP
      hstate0
      (by
        intro i hi
        exact
          (taoSection7Case3_indexedRebasedSourceUpdatesWithGap_of_indexedFirstHitSourceProvenance_splits
            (W := W) (black := black) (family := family)
            (pointAt := pointAt) (Accepts := Accepts) (n := n)
            (J := J) (xi := xi) (epsilon := epsilon) (P := P)
            (threshold := threshold) (Rtail := Rtail)
            (gapBound := gapBound) t tri j s pre pres candidate before
            next after hfull hsrc hsplit hidx hroom_next hfacts haccept
            hj_next hs_next hpre_next hpres_next i hi).to_sourceStateUpdate)

theorem taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_indexedRebasedSourceUpdates
    {W : ℕ → Prop} {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {P threshold Rtail : ℕ} {gapBound : ℕ → ℕ}
    (t : ℕ → ℕ) (tri : ℕ → TaoSection7Triangle)
    (j : ℕ → ℕ+) (s : ℕ → ℕ)
    (pre : ℕ → List ℕ) (pres : ℕ → List (List ℕ))
    (hinit :
      TaoSection7Case3InitialStoppingStep pointAt family (t 0) (tri 0))
    (hfirst_ltP : t 0 < P)
    (hstate0 :
      TaoSection7Case3FullWindowSourcePathDataWithGap
        W pointAt n J xi epsilon P threshold (t 0) gapBound
        (j 0) (s 0) (pre 0) (pres 0))
    (hupdates :
      ∀ i : ℕ, i < Rtail →
        TaoSection7Case3IndexedRebasedSourceUpdateWithGap
          (W := W) (black := black) (family := family)
          (pointAt := pointAt) (Accepts := Accepts) (n := n)
          (J := J) (xi := xi) (epsilon := epsilon) (P := P)
          (threshold := threshold) (gapBound := gapBound)
          t tri j s pre pres i) :
    TaoSection7Case3PrefixRInputs
        black family pointAt Accepts P (Rtail + 1) (t 0) (tri 0)
        (taoSection7Case3IndexedEncounterTail t tri 0 Rtail) ∧
      ∀ i : ℕ, i ≤ Rtail →
        TaoSection7Case3FullWindowSourcePathDataWithGap
          W pointAt n J xi epsilon P threshold (t i) gapBound
          (j i) (s i) (pre i) (pres i) := by
  exact
    taoSection7Case3_prefixRInputs_and_stateInvariantWithGap_of_indexedSourceStateUpdates
      (black := black) (family := family) (pointAt := pointAt)
      (Accepts := Accepts) (n := n) (J := J) (xi := xi)
      (epsilon := epsilon) (P := P) (threshold := threshold)
      (gapBound := gapBound) t tri j s pre pres hinit hfirst_ltP
      hstate0
      (by
        intro i hi
        exact
          (hupdates i hi).to_sourceStateUpdate)

end Tao
end Erdos1135
