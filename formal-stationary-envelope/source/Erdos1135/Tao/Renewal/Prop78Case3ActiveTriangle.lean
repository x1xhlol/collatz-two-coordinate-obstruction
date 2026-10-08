import Erdos1135.Tao.Renewal.SourcePathData

/-!
# Section 7 Case 3 Active-Triangle Support

This module separates the checked local black-pivot package from the still-open
active-triangle and stopping-state provenance needed by Tao's Proposition 7.8
Case 3 iteration.

It is support-only.  It does not prove that `old` is produced by Tao's stopping
process, does not prove that the later triangle is accepted by that process, and
does not prove source `(7.11)`, source `r`/`t_R`, Lemma 7.9, Lemma 7.10,
Tao's many-whites inequality, `(7.41)`, Proposition 7.8, Proposition 7.3/7.1,
or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

/--
The active/current triangle membership data at the Case 3 pivot.

These facts must come from a future stopping/iteration layer; they are not
derived from source-path data.  This structure intentionally carries no color
or current-state predicate; old-pivot blackness is a separate future obligation.
-/
structure TaoSection7Case3ActiveTriangleAt
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (A q : ℕ) (old : TaoSection7Triangle) : Prop where
  old_mem_family : old ∈ family
  pivot_mem : old.Mem (pointAt q)
  small_size : old.size < taoSection7Case3LargeTriangleBound A q

/--
Generic-bound active/current triangle membership data at the Case 3 pivot.

This is the base-aware analogue of `TaoSection7Case3ActiveTriangleAt`; it
keeps the small-triangle threshold synchronized with a caller-supplied
`bound`.
-/
structure TaoSection7Case3ActiveTriangleAtWithBound
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (bound : ℕ → ℝ) (q : ℕ) (old : TaoSection7Triangle) : Prop where
  old_mem_family : old ∈ family
  pivot_mem : old.Mem (pointAt q)
  small_size : old.size < bound q

/-- Project a family right-edge strip bound to the active old triangle. -/
theorem TaoSection7Case3ActiveTriangleAt.rightEdgeInStrip
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A q : ℕ} {old : TaoSection7Triangle} {cutoff : ℝ}
    (hactive : TaoSection7Case3ActiveTriangleAt family pointAt A q old)
    (hright : TaoSection7TriangleFamilyRightEdgeInStrip cutoff family) :
    TaoSection7TriangleRightEdgeInStrip cutoff old :=
  hright hactive.old_mem_family

/--
Local later-black-pivot data together with explicit active-triangle provenance
for the old triangle.
-/
structure TaoSection7Case3ActiveBlackPivotStep
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (A q : ℕ) (old Γ : TaoSection7Triangle) (candidate : ℕ) : Prop where
  active : TaoSection7Case3ActiveTriangleAt family pointAt A q old
  pivot_step : taoSection7Case3BlackPivotStep black family pointAt old Γ candidate

structure TaoSection7Case3ActiveBlackPivotStepWithBound
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (bound : ℕ → ℝ) (q : ℕ)
    (old Γ : TaoSection7Triangle) (candidate : ℕ) : Prop where
  active : TaoSection7Case3ActiveTriangleAtWithBound family pointAt bound q old
  pivot_step : taoSection7Case3BlackPivotStep black family pointAt old Γ candidate

theorem TaoSection7Case3ActiveBlackPivotStep.old_mem_family
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A q : ℕ} {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hstep :
      TaoSection7Case3ActiveBlackPivotStep
        black family pointAt A q old Γ candidate) :
    old ∈ family :=
  hstep.active.old_mem_family

theorem TaoSection7Case3ActiveBlackPivotStep.new_mem_family
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A q : ℕ} {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hstep :
      TaoSection7Case3ActiveBlackPivotStep
        black family pointAt A q old Γ candidate) :
    Γ ∈ family :=
  hstep.pivot_step.2.2.1

theorem TaoSection7Case3ActiveBlackPivotStep.new_ne_old
    {black : TaoSection7Point → Prop}
    {family : Set TaoSection7Triangle}
    {pointAt : ℕ → TaoSection7Point}
    {A q : ℕ} {old Γ : TaoSection7Triangle} {candidate : ℕ}
    (hstep :
      TaoSection7Case3ActiveBlackPivotStep
        black family pointAt A q old Γ candidate) :
    Γ ≠ old :=
  hstep.pivot_step.2.2.2.2

/--
Source-path data plus explicit active-triangle state gives an active-triangle
black-pivot package.

The active state itself and any stopping/iteration update remain future
producer obligations.
-/
theorem taoSection7Case3_exists_activeBlackPivotStep_of_sourcePathData
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
              ∃ Γ : TaoSection7Triangle,
                TaoSection7Case3ActiveBlackPivotStep
                  (taoSection7SourceBlackInDomain n xi epsilon J)
                  family pointAt A q old Γ candidate := by
  rcases
      taoSection7Case3_exists_laterBlackPivotStep_of_sourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hlow hroom hactive.pivot_mem hactive.small_size hcover with
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ, hΓ⟩
  exact
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ,
      ⟨hactive, hΓ⟩⟩

theorem taoSection7Case3_exists_activeBlackPivotStep_of_sourcePathData_scale
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
    ∃ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) ∧
        ¬ W candidate ∧
          taoSection7Case3HeightExitBound gapBound q < candidate ∧
            candidate < P ∧ candidate - q ≤ pres.length ∧
              ∃ Γ : TaoSection7Triangle,
                TaoSection7Case3ActiveBlackPivotStepWithBound
                  (taoSection7SourceBlackInDomain n xi epsilon J)
                  family pointAt bound q old Γ candidate := by
  rcases
      taoSection7Case3_exists_laterBlackPivotStep_of_sourcePathData_scale
        (W := W) (pointAt := pointAt) (n := n) (J := J)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (bound := bound) (gapBound := gapBound) (P := P)
        (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hscale hlow hroom hactive.pivot_mem hactive.small_size hcover with
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ, hΓ⟩
  exact
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ,
      ⟨hactive, hΓ⟩⟩

/--
An active black-pivot step accepted by an external stopping/iteration relation.

The relation `Accepts` is intentionally a caller-supplied premise; proving it is
the future first-stopping/new-triangle compatibility obligation.
-/
structure TaoSection7Case3AcceptedTriangleTransition
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    (A q : ℕ) (old Γ : TaoSection7Triangle) (candidate : ℕ) : Prop where
  active_step :
    TaoSection7Case3ActiveBlackPivotStep
      black family pointAt A q old Γ candidate
  accepted : Accepts q old candidate Γ

structure TaoSection7Case3AcceptedTriangleTransitionWithBound
    (black : TaoSection7Point → Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ → TaoSection7Point)
    (Accepts : ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
    (bound : ℕ → ℝ) (q : ℕ)
    (old Γ : TaoSection7Triangle) (candidate : ℕ) : Prop where
  active_step :
    TaoSection7Case3ActiveBlackPivotStepWithBound
      black family pointAt bound q old Γ candidate
  accepted : Accepts q old candidate Γ

/--
Source-path data plus active-triangle state gives an accepted transition only
when the caller supplies the future stopping/iteration acceptance theorem for
the produced active black-pivot step.
-/
theorem taoSection7Case3_exists_acceptedTriangleTransition_of_sourcePathData
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (Accepts :
      ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
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
      ∀ candidate Γ,
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
        TaoSection7Case3ActiveBlackPivotStep
          (taoSection7SourceBlackInDomain n xi epsilon J)
          family pointAt A q old Γ candidate →
        Accepts q old candidate Γ) :
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
                TaoSection7Case3AcceptedTriangleTransition
                  (taoSection7SourceBlackInDomain n xi epsilon J)
                  family pointAt Accepts A q old Γ candidate := by
  rcases
      taoSection7Case3_exists_activeBlackPivotStep_of_sourcePathData
        (W := W) (pointAt := pointAt) (n := n) (J := J) (A := A)
        (xi := xi) (epsilon := epsilon) (family := family) (old := old)
        (P := P) (threshold := threshold) (q := q) (j := j) (s := s)
        (pre := pre) (pres := pres)
        hdata hlow hroom hactive hcover with
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ, hstep⟩
  exact
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ,
      ⟨hstep, haccept candidate Γ hmem hnotW hstrict hltP hlen hstep⟩⟩

theorem taoSection7Case3_exists_acceptedTriangleTransition_of_sourcePathData_scale
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (Accepts :
      ℕ → TaoSection7Triangle → ℕ → TaoSection7Triangle → Prop)
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
    (haccept :
      ∀ candidate Γ,
        candidate ∈ Finset.Icc
          (taoSection7Case3LaterSearchStart gapBound q)
          (taoSection7Case3LaterSearchStart gapBound q + threshold) →
        ¬ W candidate →
        taoSection7Case3HeightExitBound gapBound q < candidate →
        candidate < P →
        candidate - q ≤ pres.length →
        TaoSection7Case3ActiveBlackPivotStepWithBound
          (taoSection7SourceBlackInDomain n xi epsilon J)
          family pointAt bound q old Γ candidate →
        Accepts q old candidate Γ) :
    ∃ candidate : ℕ,
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) ∧
        ¬ W candidate ∧
          taoSection7Case3HeightExitBound gapBound q < candidate ∧
            candidate < P ∧ candidate - q ≤ pres.length ∧
              ∃ Γ : TaoSection7Triangle,
                TaoSection7Case3AcceptedTriangleTransitionWithBound
                  (taoSection7SourceBlackInDomain n xi epsilon J)
                  family pointAt Accepts bound q old Γ candidate := by
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
    ⟨candidate, hmem, hnotW, hstrict, hltP, hlen, Γ,
      ⟨hstep, haccept candidate Γ hmem hnotW hstrict hltP hlen hstep⟩⟩

end Tao
end Erdos1135
