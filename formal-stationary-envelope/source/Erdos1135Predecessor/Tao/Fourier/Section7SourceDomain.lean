/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7SourceFThreeQFinite
import Erdos1135Predecessor.Tao.Fourier.Section7SourcePredicates

namespace Erdos1135Predecessor

namespace Tao

noncomputable def taoSection7SourceWhiteWCutoff
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ) :
    ℕ → ℤ → Prop :=
  fun j l =>
    ∃ hj : 0 < j,
      j ≤ J ∧
        taoSection7SourceWhitePoint n xi epsilon
          ({ j := ⟨j, hj⟩, l := l } : TaoSection7Point)

theorem taoSection7SourceWhiteWCutoff_raw
    {n J j : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ} {l : ℤ}
    (h : taoSection7SourceWhiteWCutoff n xi epsilon J j l) :
    taoSection7SourceWhiteW n xi epsilon j l := by
  rcases h with ⟨hj, _hJ, hwhite⟩
  exact ⟨hj, by simpa [taoSection7SourceWhitePoint] using hwhite⟩

theorem taoSection7SourceWhiteWCutoff_false_of_lt
    {n J j : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ} {l : ℤ}
    (hJ : J < j) :
    ¬ taoSection7SourceWhiteWCutoff n xi epsilon J j l := by
  rintro ⟨_hj, hjJ, _hwhite⟩
  omega

theorem taoSection7WhiteHitPenalty_cutoff_take_eq
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ) (bs : List ℕ) :
    taoSection7WhiteHitPenalty epsilon
        (taoSection7SourceWhiteWCutoff n xi epsilon J) (bs.take J) =
      taoSection7WhiteHitPenalty epsilon
        (taoSection7SourceWhiteWCutoff n xi epsilon J) bs := by
  exact taoSection7WhiteHitPenalty_take_eq_of_false_after _ _ J bs
    (fun j l hj => taoSection7SourceWhiteWCutoff_false_of_lt hj)

theorem taoSection7SourceFThreeFactor_hit_bound_cutoff
    (n : ℕ) (xi : ZMod (3 ^ n)) {epsilon : ℝ} (J : ℕ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∀ j s b,
      b = 3 ∧
          taoSection7SourceWhiteWCutoff n xi epsilon J j (Int.ofNat (s + b)) →
        taoSection7SourceFThreeFactor n xi j s b ≤
          Real.exp (-(epsilon ^ 3)) := by
  intro j s b hhit
  exact taoSection7SourceFThreeFactor_hit_bound n xi hepsilon0 hepsilon1
    j s b ⟨hhit.1, taoSection7SourceWhiteWCutoff_raw hhit.2⟩

theorem taoSection7SourceFThreeFactorProduct_take_sourceBlocks_le_qfinite_cutoff
    (n : ℕ) (xi : ZMod (3 ^ n)) {epsilon : ℝ} (J : ℕ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (pre : List ℕ) (pres : List (List ℕ))
    (hpre : taoSection7NoThree pre)
    (hpres : ∀ q ∈ pres, taoSection7NoThree q) :
    taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi)
        ((taoSection7SourceBlocks (pre :: pres)).take J) ≤
      taoSection7QFinite epsilon
        (taoSection7SourceWhiteRenewal
          (taoSection7SourceWhiteWCutoff n xi epsilon J))
        (taoSection7SourceHitPoint (1 : ℕ+) 0 pre)
        (taoSection7HoldIncrementsOfPrefixes pres) := by
  calc
    _ ≤ taoSection7WhiteHitPenalty epsilon
          (taoSection7SourceWhiteWCutoff n xi epsilon J)
          ((taoSection7SourceBlocks (pre :: pres)).take J) := by
      exact taoSection7FactorProduct_le_penalty
        (taoSection7SourceFThreeFactor_nonneg n xi)
        (taoSection7SourceFThreeFactor_hit_bound_cutoff
          n xi J hepsilon0 hepsilon1)
        (fun j s b _hmiss =>
          taoSection7SourceFThreeFactor_le_one n xi j s b) _
    _ = taoSection7WhiteHitPenalty epsilon
          (taoSection7SourceWhiteWCutoff n xi epsilon J)
          (taoSection7SourceBlocks (pre :: pres)) :=
      taoSection7WhiteHitPenalty_cutoff_take_eq n xi epsilon J _
    _ = _ := taoSection7WhiteHitPenalty_blocks_eq_qfinite
      epsilon _ pre pres hpre hpres

end Tao

end Erdos1135Predecessor
