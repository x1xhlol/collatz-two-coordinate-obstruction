/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79Recurrence

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem lemma79CutoffWhiteCount_one_le_of_white_at
    {pointAt : ℕ -> TaoSection7Point}
    {n C K : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hK : 0 < K)
    (hwhite :
      taoSection7SourceWhiteWCutoff n xi epsilon C
        ((pointAt K).j : ℕ) (pointAt K).l) :
    1 ≤ lemma79CutoffWhiteCount pointAt n xi epsilon C K := by
  unfold lemma79CutoffWhiteCount
  have hmem : K ∈ Finset.Icc 1 K := by
    simp only [Finset.mem_Icc]
    omega
  have hsingle :
      (if taoSection7SourceWhiteWCutoff n xi epsilon C
          ((pointAt K).j : ℕ) (pointAt K).l then 1 else 0) ≤
        ∑ q ∈ Finset.Icc 1 K,
          if taoSection7SourceWhiteWCutoff n xi epsilon C
              ((pointAt q).j : ℕ) (pointAt q).l then 1 else 0 :=
    Finset.single_le_sum
      (f := fun q =>
        if taoSection7SourceWhiteWCutoff n xi epsilon C
            ((pointAt q).j : ℕ) (pointAt q).l then 1 else 0)
      (fun _ _ => Nat.zero_le _) hmem
  simpa [hwhite] using hsingle

theorem lemma79HoldPathCutoffTailMoment_one_le_exp_total
    {n C : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family) :
    lemma79CutoffTailMoment
        (lemma79HoldPathPointAt start full)
        family n xi epsilon C 1 ≤ Real.exp epsilon := by
  have htrace :=
    lemma79CutoffTrace_spec
      (lemma79HoldPathPointAt start full) family C
  cases hsteps :
      lemma79CutoffTrace
        (lemma79HoldPathPointAt start full) family C with
  | nil =>
      rw [lemma79CutoffTailMoment_eq_zero_of_trace_eq_nil
        (R := 1) (by omega) hsteps]
      exact (Real.exp_pos epsilon).le
  | cons step rest =>
      rcases step with ⟨p, old⟩
      rw [hsteps] at htrace
      exact lemma79HoldPathCutoffTailMoment_one_le_exp
        hpair hcover htrace

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
