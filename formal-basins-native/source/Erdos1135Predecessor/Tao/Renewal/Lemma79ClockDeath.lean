/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79CutoffStatistic
import Erdos1135Predecessor.Tao.Renewal.Lemma79FirstExit

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

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

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
