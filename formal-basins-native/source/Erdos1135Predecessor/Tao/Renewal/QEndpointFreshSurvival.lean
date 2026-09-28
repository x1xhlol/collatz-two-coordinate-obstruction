/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79CanonicalTraceProjection
import Erdos1135Predecessor.Tao.Renewal.Lemma79Case3EventAdapter
import Erdos1135Predecessor.Tao.Renewal.PathGrowth
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshPriorityPartition
import Erdos1135Predecessor.Tao.Renewal.QEndpointFreshSupport

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def lemma79CanonicalSurvivalMaxTime
    (base Kcut T R : ℕ) : ℕ :=
  ((taoSection7Case3BaseKcutNextBound base Kcut T)^[R - 1]) T

noncomputable def lemma79CanonicalEndpointFreshEStarEvent
    (entry : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (base Kcut T R : ℕ) :
    Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
  {atom | ∃ p : ℕ,
    p ≤ lemma79CanonicalSurvivalMaxTime base Kcut T R ∧
    ∃ Delta : TaoSection7Triangle,
      Delta ∈ family ∧
      Delta.Mem (lemma79EndpointFreshPointAt entry atom p) ∧
      taoSection7Case3LargeTriangleBoundWithBase
          (base : ℝ) Kcut p ≤ Delta.size}

theorem lemma79CanonicalEndpointFreshEStarEvent_size_lt_of_not_mem
    {entry : TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {base Kcut T R p : ℕ}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    (hnot : atom ∉ lemma79CanonicalEndpointFreshEStarEvent
      entry family base Kcut T R)
    (hp : p ≤ lemma79CanonicalSurvivalMaxTime base Kcut T R)
    {Delta : TaoSection7Triangle}
    (hDelta : Delta ∈ family)
    (hmem : Delta.Mem (lemma79EndpointFreshPointAt entry atom p)) :
    Delta.size <
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p := by
  by_contra hnotLt
  exact hnot ⟨p, hp, Delta, hDelta, hmem, le_of_not_gt hnotLt⟩

theorem lemma79CanonicalSurvivalMaxTime_lt_of_iterateRoom
    {base Kcut T R P : ℕ}
    (hroom : taoSection7Case3BaseKcutNextBoundIterateRoom
      base Kcut T (R - 1) T P) :
    lemma79CanonicalSurvivalMaxTime base Kcut T R < P := by
  exact taoSection7Case3_baseKcutNextBound_iterate_lt_of_iterateRoom
    hroom (Nat.le_refl (R - 1))

theorem lemma79CanonicalSurvivalIterate_le_maxTime
    {base Kcut T R i : ℕ}
    (hi : i ≤ R - 1) :
    ((taoSection7Case3BaseKcutNextBound base Kcut T)^[i]) T ≤
      lemma79CanonicalSurvivalMaxTime base Kcut T R := by
  exact taoSection7Case3_baseKcutNextBound_iterate_le_iterate_of_le
    (base := base) (Kcut := Kcut) (T := T) (start := T) hi

theorem lemma79CanonicalEndpointFresh_exists_triangleHit_in_block
    {n P T : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {entry : TaoSection7RenewalPoint}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    (hlow : atom ∈ lemma79CanonicalEndpointFreshLowWhiteEvent
      n P T xi epsilon entry)
    (hdomain : ∀ p, p ≤ P ->
      taoSection7SourcePointInDomain (n / 2)
        (lemma79EndpointFreshPointAt entry atom p))
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family)
    {start : ℕ}
    (hblock : start + T < P) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + T) ∧
      TaoSection7Case3TriangleHit
        (lemma79EndpointFreshPointAt entry atom) family q := by
  let W := lemma79CanonicalEndpointFreshCutoffW n xi epsilon entry atom
  have hlow' : taoSection7Case3WindowWhiteCount W P ≤ T := by
    simpa [W, lemma79CanonicalEndpointFreshLowWhiteEvent,
      taoSection7Case3LowWhiteEvent, taoSection7Case3LowWhite] using hlow
  have hWwhite : ∀ q : ℕ, q ∈ Finset.Icc start (start + T) ->
      (W q ↔ taoSection7SourceWhitePoint n xi epsilon
        (lemma79EndpointFreshPointAt entry atom q)) := by
    intro q hq
    have hqBounds := Finset.mem_Icc.mp hq
    have hqP : q ≤ P := by omega
    have hqDomain := hdomain q hqP
    simp [W, lemma79CanonicalEndpointFreshCutoffW,
      taoSection7Case3SourceCutoffPointW, hqDomain]
  have hdomainBlock : ∀ q : ℕ,
      q ∈ Finset.Icc start (start + T) ->
      taoSection7SourcePointInDomain (n / 2)
        (lemma79EndpointFreshPointAt entry atom q) := by
    intro q hq
    have hqBounds := Finset.mem_Icc.mp hq
    exact hdomain q (by omega)
  rcases taoSection7Case3_low_window_produces_source_triangle_offset
      W (lemma79EndpointFreshPointAt entry atom)
      hlow' hblock hWwhite hdomainBlock hcover with
    ⟨q, hq, _hnotW, Delta, hDelta, hmem⟩
  exact ⟨q, hq, Delta, hDelta, hmem⟩

theorem lemma79CanonicalEndpointFresh_afterTriangleHit_of_small
    {entry : TaoSection7RenewalPoint}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    {base Kcut q candidate : ℕ}
    {Delta : TaoSection7Triangle}
    (hall : taoSection7AllHoldIncrementsLGeOne atom.2)
    (hcandidateLen : candidate ≤ atom.2.length)
    (hqc : q ≤ candidate)
    (hstrict :
      taoSection7Case3HeightExitBound
        (taoSection7Case3ExitGapBoundWithBase base Kcut) q < candidate)
    (hDeltaMem : Delta.Mem (lemma79EndpointFreshPointAt entry atom q))
    (hDeltaSize : Delta.size <
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut q)
    (hhit : TaoSection7Case3TriangleHit
      (lemma79EndpointFreshPointAt entry atom) family candidate) :
    TaoSection7Case3AfterTriangleHit
      (lemma79EndpointFreshPointAt entry atom) family Delta candidate := by
  have hdropLen : candidate - q ≤ (atom.2.drop q).length := by
    rw [List.length_drop]
    omega
  have hdropAll :
      taoSection7AllHoldIncrementsLGeOne (atom.2.drop q) := by
    intro h hh
    exact hall h (List.mem_of_mem_drop hh)
  have hgrowth := taoSection7Case3_sourceVerticalGrowth_of_scale_path
    (p := taoSection7RenewalPathPoint
      (lemma79EndpointFreshOrigin entry atom) atom.2 q)
    (holds := atom.2.drop q)
    (bound := taoSection7Case3LargeTriangleBoundWithBase
      (base : ℝ) Kcut)
    (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
    (q := q) (candidate := candidate)
    (taoSection7Case3RecurrenceScale_baseKcut base Kcut)
    hstrict hdropLen hdropAll
  have hgrowth' :
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut q ≤
        ((((lemma79EndpointFreshPointAt entry atom candidate).l -
          (lemma79EndpointFreshPointAt entry atom q).l : ℤ) : ℝ) *
            Real.log 2) := by
    simpa [lemma79EndpointFreshPointAt,
      taoSection7RenewalPathPoint_drop_candidate_sub hqc] using hgrowth
  exact ⟨
    taoSection7Case3_cornerL_lt_of_mem_and_vertical_growth_log2_gt_size
      hDeltaMem (lt_of_lt_of_le hDeltaSize hgrowth'),
    hhit⟩

theorem lemma79CanonicalEndpointFresh_exists_next_stop
    {n P T R base Kcut : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {entry : TaoSection7RenewalPoint}
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    (hlow : atom ∈ lemma79CanonicalEndpointFreshLowWhiteEvent
      n P T xi epsilon entry)
    (hdomain : ∀ p, p ≤ P ->
      taoSection7SourcePointInDomain (n / 2)
        (lemma79EndpointFreshPointAt entry atom p))
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family)
    (hall : taoSection7AllHoldIncrementsLGeOne atom.2)
    (hPLength : P ≤ atom.2.length)
    (hnotEStar : atom ∉ lemma79CanonicalEndpointFreshEStarEvent
      entry family base Kcut T R)
    {q : ℕ} {Delta : TaoSection7Triangle}
    {before after : List (ℕ × TaoSection7Triangle)}
    (hdecomp : lemma79CutoffTrace
      (lemma79EndpointFreshPointAt entry atom) family (n / 2) =
        before ++ (q, Delta) :: after)
    (hqMax : q ≤ lemma79CanonicalSurvivalMaxTime base Kcut T R)
    (hDeltaFamily : Delta ∈ family)
    (hDeltaMem : Delta.Mem (lemma79EndpointFreshPointAt entry atom q))
    (hnextP : taoSection7Case3BaseKcutNextBound base Kcut T q < P)
    (hP : P ≤ n / 2) :
    ∃ qNext Gamma rest,
      lemma79CutoffTrace
          (lemma79EndpointFreshPointAt entry atom) family (n / 2) =
        before ++ (q, Delta) :: (qNext, Gamma) :: rest ∧
      qNext ≤ taoSection7Case3BaseKcutNextBound base Kcut T q ∧
      Gamma ∈ family ∧
      Gamma.Mem (lemma79EndpointFreshPointAt entry atom qNext) := by
  let gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut
  let start := taoSection7Case3LaterSearchStart gapBound q
  have hblock : start + T < P := by
    simpa [start, gapBound, taoSection7Case3BaseKcutNextBound,
      taoSection7Case3LaterSearchBound] using hnextP
  rcases lemma79CanonicalEndpointFresh_exists_triangleHit_in_block
      hlow hdomain hcover hblock with
    ⟨candidate, hcandidate, hhit⟩
  have hcandidateBounds := Finset.mem_Icc.mp hcandidate
  have hstrict : taoSection7Case3HeightExitBound gapBound q < candidate := by
    dsimp [start, taoSection7Case3LaterSearchStart] at hcandidateBounds
    omega
  have hqc : q ≤ candidate := by
    dsimp [gapBound, taoSection7Case3HeightExitBound] at hstrict
    omega
  have hcandidateP : candidate < P :=
    lt_of_le_of_lt hcandidateBounds.2 hblock
  have hcandidateLen : candidate ≤ atom.2.length :=
    le_trans (Nat.le_of_lt hcandidateP) hPLength
  have hDeltaSize :=
    lemma79CanonicalEndpointFreshEStarEvent_size_lt_of_not_mem
      hnotEStar hqMax hDeltaFamily hDeltaMem
  have hafter : TaoSection7Case3AfterTriangleHit
      (lemma79EndpointFreshPointAt entry atom) family Delta candidate :=
    lemma79CanonicalEndpointFresh_afterTriangleHit_of_small
      hall hcandidateLen hqc (by simpa [gapBound] using hstrict)
      hDeltaMem hDeltaSize hhit
  rcases lemma79CutoffTrace_next_of_decomp_of_afterTriangleHit
      hdecomp (lt_of_lt_of_le (by
        dsimp [gapBound, taoSection7Case3HeightExitBound] at hstrict
        omega) le_rfl)
      (lt_of_lt_of_le hcandidateP hP) hafter with
    ⟨qNext, Gamma, rest, hnextDecomp, hqNext, hstep⟩
  have hcandidateNext :
      candidate ≤ taoSection7Case3BaseKcutNextBound base Kcut T q := by
    exact hcandidateBounds.2
  exact ⟨qNext, Gamma, rest, hnextDecomp,
    hqNext.trans hcandidateNext, hstep.new_mem_family, hstep.new_mem⟩

theorem lemma79CanonicalEndpointFreshPMF_surviveWithinP_of_middle_not_eStar
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (family : Set TaoSection7Triangle)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family)
    (entry : TaoSection7RenewalPoint)
    (gap P m T R base Kcut : ℕ)
    (hboundary : taoSection7QmBoundary (n / 2) m entry)
    (hP : P ≤ n / 2)
    (hR : 0 < R)
    (hroom : taoSection7Case3BaseKcutNextBoundIterateRoom
      base Kcut T (R - 1) T P)
    {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint}
    (hne : lemma79CanonicalEndpointFreshPMF
      (n / 2) entry gap atom ≠ 0)
    (hnotBad : atom ∉ lemma79CanonicalEndpointFreshOuterBadJEvent P m)
    (hlow : atom ∈ lemma79CanonicalEndpointFreshLowWhiteEvent
      n P T xi epsilon entry)
    (hnotEStar : atom ∉ lemma79CanonicalEndpointFreshEStarEvent
      entry family base Kcut T R) :
    atom.2 ∈ lemma79CanonicalSurviveWithinPEvent
      (lemma79EndpointFreshOrigin entry atom) family (n / 2) R P := by
  let pointAt := lemma79EndpointFreshPointAt entry atom
  let steps := lemma79CutoffTrace pointAt family (n / 2)
  let Next := taoSection7Case3BaseKcutNextBound base Kcut T
  have hdomainData :=
    lemma79CanonicalEndpointFreshPMF_sourceDomain_of_not_largeHorizontal
      hboundary hP hne (by
        simpa [lemma79CanonicalEndpointFreshOuterBadJEvent] using hnotBad)
  have hPLength : P ≤ atom.2.length := hdomainData.1
  have hdomain : ∀ p, p ≤ P ->
      taoSection7SourcePointInDomain (n / 2) (pointAt p) := by
    simpa [pointAt] using hdomainData.2
  have hall : taoSection7AllHoldIncrementsLGeOne atom.2 :=
    lemma79CanonicalEndpointFreshPMF_fresh_all_l_ge_one hne
  have hmaxP : lemma79CanonicalSurvivalMaxTime base Kcut T R < P :=
    lemma79CanonicalSurvivalMaxTime_lt_of_iterateRoom hroom
  have hTMax : T ≤ lemma79CanonicalSurvivalMaxTime base Kcut T R := by
    simpa using
      (lemma79CanonicalSurvivalIterate_le_maxTime
        (base := base) (Kcut := Kcut) (T := T) (R := R) (i := 0)
        (Nat.zero_le (R - 1)))
  have hTP : T < P := lt_of_le_of_lt hTMax hmaxP
  rcases lemma79CanonicalEndpointFresh_exists_triangleHit_in_block
      hlow hdomain hcover (start := 0) (by simpa using hTP) with
    ⟨candidate, hcandidate, hcandidateHit⟩
  have hcandidateBounds := Finset.mem_Icc.mp hcandidate
  have hcandidateCutoff : candidate < n / 2 :=
    lt_of_le_of_lt hcandidateBounds.2 (by omega)
  rcases lemma79CutoffTrace_exists_first_le_of_hit
      hcandidateCutoff (by simpa [pointAt] using hcandidateHit) with
    ⟨q0, Delta0, after0, hsteps0, hq0Candidate,
      _hfirst0, hDelta0Family, hDelta0Mem⟩
  have hq0T : q0 ≤ T :=
    hq0Candidate.trans (by simpa using hcandidateBounds.2)
  have hind : ∀ k : ℕ, k ≤ R - 1 ->
      ∃ before q Delta after,
        before.length = k ∧
        steps = before ++ (q, Delta) :: after ∧
        q ≤ (Next^[k]) T ∧
        Delta ∈ family ∧ Delta.Mem (pointAt q) := by
    intro k hk
    induction k with
    | zero =>
        exact ⟨[], q0, Delta0, after0, rfl,
          by simpa [steps, pointAt] using hsteps0,
          by simpa using hq0T, hDelta0Family,
          by simpa [pointAt] using hDelta0Mem⟩
    | succ k ih =>
        have hkPrev : k ≤ R - 1 := le_trans (Nat.le_succ k) hk
        rcases ih hkPrev with
          ⟨before, q, Delta, after, hbeforeLength, hdecomp,
            hqIter, hDeltaFamily, hDeltaMem⟩
        have hqMax :
            q ≤ lemma79CanonicalSurvivalMaxTime base Kcut T R :=
          hqIter.trans
            (lemma79CanonicalSurvivalIterate_le_maxTime hkPrev)
        have hnextIter :
            Next q ≤ (Next^[k + 1]) T := by
          calc
            Next q ≤ Next ((Next^[k]) T) :=
              taoSection7Case3BaseKcutNextBound_mono base Kcut T hqIter
            _ = (Next^[k + 1]) T := by
              simp [Function.iterate_succ_apply']
        have hnextP : Next q < P :=
          hnextIter.trans_lt
            (taoSection7Case3_baseKcutNextBound_iterate_lt_of_iterateRoom
              hroom hk)
        rcases lemma79CanonicalEndpointFresh_exists_next_stop
            hlow hdomain hcover hall hPLength hnotEStar
            (by simpa [steps, pointAt] using hdecomp)
            hqMax hDeltaFamily (by simpa [pointAt] using hDeltaMem)
            (by simpa [Next] using hnextP) hP with
          ⟨qNext, Gamma, rest, hnextDecomp, hqNext,
            hGammaFamily, hGammaMem⟩
        refine ⟨before ++ [(q, Delta)], qNext, Gamma, rest, ?_, ?_, ?_,
          hGammaFamily, ?_⟩
        · simp [hbeforeLength]
        · simpa [steps, pointAt, List.append_assoc] using hnextDecomp
        · exact hqNext.trans hnextIter
        · simpa [pointAt] using hGammaMem
  rcases hind (R - 1) le_rfl with
    ⟨before, q, Delta, after, hbeforeLength, hdecomp,
      hqMaxIter, _hDeltaFamily, _hDeltaMem⟩
  have haccess := tR?_append_cons_length_add_one before after q Delta
  have htR : tR? steps R = some q := by
    rw [← hdecomp] at haccess
    have hRLength : before.length + 1 = R := by omega
    simpa [hRLength] using haccess
  have hqP : q < P :=
    hqMaxIter.trans_lt (by simpa [Next] using hroom)
  exact ⟨q, by simpa [steps, pointAt] using htR, hqP⟩

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
