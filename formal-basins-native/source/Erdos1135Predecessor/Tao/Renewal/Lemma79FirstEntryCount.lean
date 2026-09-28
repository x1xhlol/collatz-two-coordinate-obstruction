/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma79FirstExit

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem lemma79PositiveWhiteCount_eq_pred_of_before_and_not_at
    (W : ℕ -> Prop) [DecidablePred W] (p : ℕ)
    (hbefore : ∀ q : ℕ, q < p -> W q)
    (hat : ¬ W p) :
    taoSection7Case3PositiveWhiteCount W p = p.pred := by
  cases p with
  | zero => simp [taoSection7Case3PositiveWhiteCount]
  | succ p =>
      have hprefix : taoSection7Case3PositiveWhiteCount W p = p := by
        unfold taoSection7Case3PositiveWhiteCount
        calc
          (Finset.Icc 1 p).sum (fun q => if W q then 1 else 0) =
              (Finset.Icc 1 p).sum (fun _q => 1) := by
                apply Finset.sum_congr rfl
                intro q hq
                rw [if_pos (hbefore q (by
                  have hle := (Finset.mem_Icc.mp hq).2
                  omega))]
          _ = (Finset.Icc 1 p).card := by simp
          _ = p := by simp
      rw [lemma79PositiveWhiteCount_succ, hprefix, if_neg hat]
      simp

theorem lemma79HoldPathPoint_j_mono
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    {q p : ℕ} (hqp : q ≤ p) :
    ((lemma79HoldPathPointAt start full q).j : ℕ) ≤
      ((lemma79HoldPathPointAt start full p).j : ℕ) := by
  let u := p - q
  have hqu : q + u = p := Nat.add_sub_of_le hqp
  let atQ := taoSection7RenewalPathPoint start full q
  have hj :=
    TaoSection7Lemma77.lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta
      atQ u (full.drop q)
  have hpath := taoSection7RenewalPathPoint_drop_add start full q u
  change ((taoSection7RenewalPathPoint start full q).j : ℕ) ≤
    ((taoSection7RenewalPathPoint start full p).j : ℕ)
  rw [← hqu, ← hpath]
  dsimp [atQ] at hj
  omega

theorem lemma79HoldPathCutoffWhiteCount_firstEntry
    {n C p : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hfirst : Lemma79FirstTriangleHitFromZero
      (lemma79HoldPathPointAt start full) family p) :
    lemma79CutoffWhiteCount
      (lemma79HoldPathPointAt start full) n xi epsilon C p = p.pred := by
  let pointAt := lemma79HoldPathPointAt start full
  let W : ℕ -> Prop := fun q =>
    taoSection7SourceWhiteWCutoff n xi epsilon C
      ((pointAt q).j : ℕ) (pointAt q).l
  have hentryBlack :
      taoSection7SourceBlackInDomain n xi epsilon C (pointAt p) :=
    (hcover (pointAt p)).mpr hfirst.1
  have hbefore : ∀ q : ℕ, q < p -> W q := by
    intro q hqp
    have hjmono := lemma79HoldPathPoint_j_mono start full
      (Nat.le_of_lt hqp)
    have hqDomain : ((pointAt q).j : ℕ) ≤ C := by
      have hpDomain := taoSection7SourceBlackInDomain_domain hentryBlack
      have hjmono' : ((pointAt q).j : ℕ) ≤ ((pointAt p).j : ℕ) := by
        simpa [pointAt] using hjmono
      exact hjmono'.trans hpDomain
    have hqWhitePoint :
        taoSection7SourceWhitePoint n xi epsilon (pointAt q) := by
      apply taoSection7SourceWhitePoint_iff_not_blackPoint.mpr
      intro hqBlack
      have hqBlackDomain :
          taoSection7SourceBlackInDomain n xi epsilon C (pointAt q) :=
        ⟨hqDomain, hqBlack⟩
      exact hfirst.2 q hqp ((hcover (pointAt q)).mp hqBlackDomain)
    refine ⟨(pointAt q).j.property, hqDomain, ?_⟩
    simpa [taoSection7SourceWhitePoint] using hqWhitePoint
  have hat : ¬ W p := by
    rintro ⟨_hpj, _hpC, hpWhite⟩
    have hpWhitePoint :
        taoSection7SourceWhitePoint n xi epsilon (pointAt p) := by
      simpa [taoSection7SourceWhitePoint] using hpWhite
    exact (taoSection7SourceWhitePoint_iff_not_blackPoint.mp hpWhitePoint)
      hentryBlack.2
  change taoSection7Case3PositiveWhiteCount W p = p.pred
  exact lemma79PositiveWhiteCount_eq_pred_of_before_and_not_at
    W p hbefore hat

theorem lemma79HoldPathCutoffWhiteCount_firstEntry_add
    {n C p : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hfirst : Lemma79FirstTriangleHitFromZero
      (lemma79HoldPathPointAt start full) family p)
    (K : ℕ) :
    lemma79CutoffWhiteCount
        (lemma79HoldPathPointAt start full) n xi epsilon C (p + K) =
      p.pred +
        lemma79CutoffWhiteCount
          (lemma79HoldPathRestartPointAt start full p)
          n xi epsilon C K := by
  rw [lemma79HoldPathCutoffWhiteCount_restart_add,
    lemma79HoldPathCutoffWhiteCount_firstEntry hcover hfirst]

end Lemma79TailExpectation

end TaoSection7Case3SourceStoppingRun

end

end Tao

end Erdos1135Predecessor
