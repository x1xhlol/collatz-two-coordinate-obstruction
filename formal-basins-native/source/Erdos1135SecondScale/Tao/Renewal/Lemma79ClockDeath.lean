/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79FirstExit
import Erdos1135SecondScale.Tao.Renewal.Lemma79CutoffStatistic

/-!
# Lemma 7.9 Clock-Death Branch

This deterministic proof leaf closes the killed `R=2` branch when the first
exit from the entry triangle occurs at or beyond the bounded trace cutoff.
Every second stopping transition must occur at or after that first exit, while
every retained stop lies strictly before the cutoff.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- A later stopping transition cannot precede the certified first-exit clock. -/
theorem Lemma79FirstExitCertificate.exit_le_of_stoppingTransition
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old Gamma : TaoSection7Triangle}
    {p k1 t : ℕ}
    (hexit : Lemma79FirstExitCertificate pointAt old p k1)
    (hstep :
      TaoSection7Case3StoppingTransition
        pointAt family p old t Gamma) :
    k1 ≤ t := by
  by_contra hnot
  have htk1 : t < k1 := Nat.lt_of_not_ge hnot
  exact hexit.no_afterTriangleHit_before
    hstep.first_after_exit.1 htk1 hstep.first_after_exit.2.1

/-- If the first exit is not before the cutoff, a bounded trace beginning at
the entry step has fewer than two stops. -/
theorem Lemma79BoundedInclusiveTrace.r_lt_two_of_cutoff_le_firstExit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle}
    {C p k1 : ℕ}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htrace :
      Lemma79BoundedInclusiveTrace
        pointAt family C ((p, old) :: rest))
    (hexit : Lemma79FirstExitCertificate pointAt old p k1)
    (hcut : C ≤ k1) :
    r ((p, old) :: rest) < 2 := by
  cases rest with
  | nil =>
      simp [r]
  | cons step rest =>
      rcases step with ⟨t, Gamma⟩
      have hstep :
          TaoSection7Case3StoppingTransition
            pointAt family p old t Gamma :=
        TaoSection7Case3StoppingTail.head_step
          htrace.toBoundedStoppingTail.trace_tail
      have hexit_le : k1 ≤ t :=
        hexit.exit_le_of_stoppingTransition hstep
      have htC : t < C :=
        htrace.all_stop_lt (t, Gamma) (by simp)
      omega

/-- Every repaired cutoff statistic with `R ≥ 2` vanishes when the first exit
from its entry triangle occurs at or beyond the cutoff. -/
theorem lemma79CutoffTailMoment_eq_zero_of_cutoff_le_firstExit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C p k1 R : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hR : 2 ≤ R)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace :
      Lemma79BoundedInclusiveTrace
        pointAt family C ((p, old) :: rest))
    (hexit : Lemma79FirstExitCertificate pointAt old p k1)
    (hcut : C ≤ k1) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C R = 0 := by
  have hcanonical :=
    lemma79CutoffTrace_spec pointAt family C
  have hsteps :
      (p, old) :: rest = lemma79CutoffTrace pointAt family C :=
    htrace.steps_eq_of_pairwiseDisjoint hpair hcanonical
  apply lemma79CutoffTailMoment_eq_zero_of_r_lt
  rw [← hsteps]
  exact (htrace.r_lt_two_of_cutoff_le_firstExit hexit hcut).trans_le hR

/-- The repaired `R=2` cutoff statistic vanishes when its first exit occurs
at or beyond the cutoff. -/
theorem lemma79CutoffTailMoment_two_eq_zero_of_cutoff_le_firstExit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {n C p k1 : ℕ}
    {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (htrace :
      Lemma79BoundedInclusiveTrace
        pointAt family C ((p, old) :: rest))
    (hexit : Lemma79FirstExitCertificate pointAt old p k1)
    (hcut : C ≤ k1) :
    lemma79CutoffTailMoment pointAt family n xi epsilon C 2 = 0 := by
  exact lemma79CutoffTailMoment_eq_zero_of_cutoff_le_firstExit
    (R := 2) le_rfl hpair htrace hexit hcut

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135SecondScale
