import SecondScaleCanonicalLocalClockProbability
import Erdos1135SecondScale.Tao.Section3.Prop111RealRate

namespace CollatzClockSecondScale
open Erdos1135SecondScale.Tao

noncomputable def realClockSourceY (x : ℝ) (branch : TaoSection5SourceBranch) : ℝ :=
  x ^ taoSection5BranchExponent branch

noncomputable def realClockSourceLo (x : ℝ) (branch : TaoSection5SourceBranch) : ℕ :=
  taoNyLo (realClockSourceY x branch)

noncomputable def realClockSourceHi (x : ℝ) (branch : TaoSection5SourceBranch) : ℕ :=
  taoNyHi (realClockSourceY x branch) taoAlpha

def oddEventToNat (G : Set TaoOddNat) : Set ℕ :=
  {q | ∃ hq : Odd q, (⟨q, hq⟩ : TaoOddNat) ∈ G}

theorem odd_source_event_probability_eq_logFinsetProb {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) (G : Set TaoOddNat) :
    ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure G).toReal =
      logFinsetProb (oddLogWindow lo hi) (oddEventToNat G) := by
  rw [oddLogWindowOddNatPMF, PMF.toOuterMeasure_map_apply,
    ← pmfProb_eq_toOuterMeasure_toReal, ← pmfProb_oddLogWindowPMF lo hi hmass]
  congr 1
  ext q
  constructor
  · intro hq
    exact ⟨(oddLogWindowValueToOddNat q).2, hq⟩
  · rintro ⟨hq, hG⟩
    exact hG

theorem odd_source_event_probability_perturbation
    {lo₁ hi₁ lo₂ hi₂ : ℕ} {err : ℝ}
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂))
    (hperturb : TaoLogWindowSourcePerturbation lo₁ hi₁ lo₂ hi₂ err)
    (G : Set TaoOddNat) :
    |((oddLogWindowOddNatPMF lo₁ hi₁ hmass₁).toOuterMeasure G).toReal -
      ((oddLogWindowOddNatPMF lo₂ hi₂ hmass₂).toOuterMeasure G).toReal| ≤ err := by
  rw [odd_source_event_probability_eq_logFinsetProb,
    odd_source_event_probability_eq_logFinsetProb]
  exact hperturb (oddEventToNat G)

theorem real_clock_source_mass_lower {x : ℝ}
    (facts : TaoProp111RealFloorWindowMassFacts x) (branch : TaoSection5SourceBranch) :
    Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤ logFinsetMass
      (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)) := by
  cases branch
  · exact facts.alpha_real
  · exact facts.alphaSq_real

theorem floor_clock_source_mass_lower {x : ℝ}
    (facts : TaoProp111RealFloorWindowMassFacts x) (branch : TaoSection5SourceBranch) :
    Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤ logFinsetMass
      (oddLogWindow (taoSection5SourceLo (Nat.floor x) branch)
        (taoSection5SourceHi (Nat.floor x) branch)) := by
  cases branch
  · exact facts.alpha_floor
  · exact facts.alphaSq_floor

theorem real_clock_source_mass_pos {x : ℝ}
    (facts : TaoProp111RealFloorWindowMassFacts x) (branch : TaoSection5SourceBranch) :
    0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)) :=
  (div_pos facts.log_floor_pos (by norm_num)).trans_le (real_clock_source_mass_lower facts branch)

theorem floor_clock_source_mass_pos {x : ℝ}
    (facts : TaoProp111RealFloorWindowMassFacts x) (branch : TaoSection5SourceBranch) :
    0 < logFinsetMass
      (oddLogWindow (taoSection5SourceLo (Nat.floor x) branch)
        (taoSection5SourceHi (Nat.floor x) branch)) :=
  (div_pos facts.log_floor_pos (by norm_num)).trans_le (floor_clock_source_mass_lower facts branch)

theorem real_floor_clock_source_perturbation {x : ℝ}
    (facts : TaoProp111RealFloorWindowMassFacts x) (branch : TaoSection5SourceBranch) :
    TaoLogWindowSourcePerturbation
      (realClockSourceLo x branch) (realClockSourceHi x branch)
      (taoSection5SourceLo (Nat.floor x) branch) (taoSection5SourceHi (Nat.floor x) branch)
      (taoProp111FloorSourceError (Nat.floor x)) := by
  intro G
  cases branch
  · simpa only [realClockSourceLo, realClockSourceHi, realClockSourceY,
      taoSection5BranchExponent, taoSection5SourceLo, taoSection5SourceHi,
      taoSection5SourceY, taoNyOddWindow, taoProp111FloorSourceError, abs_sub_comm] using
      abs_logFinsetProb_taoNyOddWindow_floor_taoAlpha_sub_le facts.one_le_x facts.log_floor_pos
        facts.alpha_floor facts.alpha_real G
  · simpa only [realClockSourceLo, realClockSourceHi, realClockSourceY,
      taoSection5BranchExponent, taoSection5SourceLo, taoSection5SourceHi,
      taoSection5SourceY, taoNyOddWindow, taoProp111FloorSourceError, abs_sub_comm] using
      abs_logFinsetProb_taoNyOddWindow_floor_taoAlpha_sq_sub_le facts.one_le_x facts.log_floor_pos
        facts.alphaSq_floor facts.alphaSq_real G

theorem real_source_event_probability_le_floor_add {x : ℝ}
    (facts : TaoProp111RealFloorWindowMassFacts x) (branch : TaoSection5SourceBranch)
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo x branch) (realClockSourceHi x branch)))
    (G : Set TaoOddNat) :
    ((oddLogWindowOddNatPMF (realClockSourceLo x branch) (realClockSourceHi x branch)
      hmass).toOuterMeasure G).toReal ≤
      ((oddLogWindowOddNatPMF (taoSection5SourceLo (Nat.floor x) branch)
        (taoSection5SourceHi (Nat.floor x) branch)
        (floor_clock_source_mass_pos facts branch)).toOuterMeasure G).toReal +
        taoProp111FloorSourceError (Nat.floor x) := by
  have h := odd_source_event_probability_perturbation hmass
    (floor_clock_source_mass_pos facts branch)
    (real_floor_clock_source_perturbation facts branch) G
  linarith [(abs_le.mp h).2]

end CollatzClockSecondScale

#print axioms CollatzClockSecondScale.odd_source_event_probability_eq_logFinsetProb
#print axioms CollatzClockSecondScale.odd_source_event_probability_perturbation
#print axioms CollatzClockSecondScale.real_floor_clock_source_perturbation
#print axioms CollatzClockSecondScale.real_source_event_probability_le_floor_add
