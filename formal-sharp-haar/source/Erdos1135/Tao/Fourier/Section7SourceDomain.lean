import Erdos1135.Tao.Fourier.Section7SourcePredicates
import Erdos1135.Tao.Fourier.Section7SourceFThreeQFinite

/-!
# Section 7 Source Domain Gates

This module extends the low source predicates with cutoff and renewal-facing
bridges. It does not prove Lemma 7.4 or Proposition 7.3.
-/

namespace Erdos1135
namespace Tao

/--
Cutoff-gated source white predicate for the renewal `W`.  It is false outside
the source cutoff, rather than being a complement that turns true there.
-/
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

theorem taoSection7SourceWhiteWCutoff_iff_of_le
    {n J j : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ} {l : ℤ}
    (hjJ : j ≤ J) :
    taoSection7SourceWhiteWCutoff n xi epsilon J j l ↔
      taoSection7SourceWhiteW n xi epsilon j l := by
  constructor
  · exact taoSection7SourceWhiteWCutoff_raw
  · rintro ⟨hj, hwhite⟩
    exact ⟨hj, hjJ, by simpa [taoSection7SourceWhitePoint] using hwhite⟩

theorem taoSection7SourceWhiteWCutoff_false_of_lt
    {n J j : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ} {l : ℤ}
    (hJ : J < j) :
    ¬ taoSection7SourceWhiteWCutoff n xi epsilon J j l := by
  rintro ⟨_hj, hjJ, _hwhite⟩
  omega

theorem taoSection7SourceWhiteWCutoff_false_of_cutoff_lt
    {n J j : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ} {l : ℤ}
    (hJ : J < j) :
    ¬ taoSection7SourceWhiteWCutoff n xi epsilon J j l :=
  taoSection7SourceWhiteWCutoff_false_of_lt hJ

theorem taoSection7WhiteHitCount_cutoff_take_eq
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ) (bs : List ℕ) :
    taoSection7WhiteHitCount
        (taoSection7SourceWhiteWCutoff n xi epsilon J) (bs.take J) =
      taoSection7WhiteHitCount
        (taoSection7SourceWhiteWCutoff n xi epsilon J) bs := by
  exact taoSection7WhiteHitCount_take_eq_of_false_after _ J bs
    (fun j l hj => taoSection7SourceWhiteWCutoff_false_of_lt hj)

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

theorem taoSection7SourceFThreeFactorProduct_blocks_le_qfinite_cutoff
    (n : ℕ) (xi : ZMod (3 ^ n)) {epsilon : ℝ} (J : ℕ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (pre : List ℕ) (pres : List (List ℕ))
    (hpre : taoSection7NoThree pre)
    (hpres : ∀ q ∈ pres, taoSection7NoThree q) :
    taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi)
        (taoSection7SourceBlocks (pre :: pres)) ≤
      taoSection7QFinite epsilon
        (taoSection7SourceWhiteRenewal
          (taoSection7SourceWhiteWCutoff n xi epsilon J))
        (taoSection7SourceHitPoint (1 : ℕ+) 0 pre)
        (taoSection7HoldIncrementsOfPrefixes pres) := by
  exact taoSection7FactorProduct_blocks_le_qfinite
    (taoSection7SourceFThreeFactor_nonneg n xi)
    (taoSection7SourceFThreeFactor_hit_bound_cutoff n xi J hepsilon0 hepsilon1)
    (by
      intro j s b _hmiss
      exact taoSection7SourceFThreeFactor_le_one n xi j s b)
    pre pres hpre hpres

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

theorem taoSection7SourceFThreeFactorProduct_blocks_le_qfinite_of_cutoff
    (n : ℕ) (xi : ZMod (3 ^ n)) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (pre : List ℕ) (pres : List (List ℕ))
    (hpre : taoSection7NoThree pre)
    (hpres : ∀ q ∈ pres, taoSection7NoThree q) :
    taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi)
        (taoSection7SourceBlocks (pre :: pres)) ≤
      taoSection7QFinite epsilon
        (taoSection7SourceWhiteRenewal
          (taoSection7SourceWhiteWCutoff n xi epsilon (n / 2)))
        (taoSection7SourceHitPoint (1 : ℕ+) 0 pre)
        (taoSection7HoldIncrementsOfPrefixes pres) := by
  exact taoSection7SourceFThreeFactorProduct_blocks_le_qfinite_cutoff
    n xi (J := n / 2) hepsilon0 hepsilon1 pre pres hpre hpres

/-- Source-facing Lemma 7.4 statement surface with the black domain gate baked in. -/
noncomputable def TaoSection7SourceBlackTriangleFamilyDecompositionStatement
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ) : Prop :=
  TaoSection7BlackTriangleFamilyDecompositionStatement
    (taoSection7SourceBlackInDomain n xi epsilon J)
    (taoSection7TriangleRightBound n epsilon)
    (taoSection7TriangleSeparation epsilon)

/-- Tao Lemma 7.4 statement surface at the source cutoff `J = n / 2`. -/
noncomputable def TaoSection7Lemma74BlackTriangleDecompositionStatement
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) : Prop :=
  TaoSection7BlackTriangleFamilyDecompositionStatement
    (taoSection7SourceBlackInDomain n xi epsilon (n / 2))
    (taoSection7TriangleRightBound n epsilon)
    (taoSection7TriangleSeparation epsilon)

/--
Floor-backed Lemma 7.4 statement surface exposing the real right-edge strip
field used in Tao's `(7.52)`.
-/
noncomputable def TaoSection7Lemma74BlackTriangleRightEdgeDecompositionStatement
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) : Prop :=
  ∃ family : Set TaoSection7Triangle,
    TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) family ∧
      TaoSection7TriangleFamilyPairwiseDisjoint family ∧
        TaoSection7TriangleFamilyRightEdgeInStrip ((n / 2 : ℕ) : ℝ) family ∧
          TaoSection7TriangleFamilySeparatedBy
            (taoSection7TriangleSeparation epsilon) family

theorem taoSection7WhiteHitCountFrom_cutoff_eq
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ) :
    ∀ (j s : ℕ) (bs : List ℕ),
      j + bs.length ≤ J + 1 →
        taoSection7WhiteHitCountFrom
            (taoSection7SourceWhiteWCutoff n xi epsilon J) j s bs =
          taoSection7WhiteHitCountFrom (taoSection7SourceWhiteW n xi epsilon)
            j s bs := by
  intro j s bs
  induction bs generalizing j s with
  | nil =>
      intro _hlen
      simp [taoSection7WhiteHitCountFrom]
  | cons b bs ih =>
      intro hlen
      classical
      have hlen' : j + (bs.length + 1) ≤ J + 1 := by
        simpa using hlen
      have hjJ : j ≤ J := by omega
      have htail : j + 1 + bs.length ≤ J + 1 := by omega
      have hW :
          (b = 3 ∧
              taoSection7SourceWhiteWCutoff n xi epsilon J j (Int.ofNat (s + b))) ↔
            (b = 3 ∧
              taoSection7SourceWhiteW n xi epsilon j (Int.ofNat (s + b))) := by
        constructor
        · rintro ⟨hb, hwhite⟩
          exact ⟨hb, taoSection7SourceWhiteWCutoff_raw hwhite⟩
        · rintro ⟨hb, hwhite⟩
          exact ⟨hb, (taoSection7SourceWhiteWCutoff_iff_of_le hjJ).2 hwhite⟩
      rw [taoSection7WhiteHitCountFrom, taoSection7WhiteHitCountFrom]
      by_cases hraw :
          b = 3 ∧ taoSection7SourceWhiteW n xi epsilon j (Int.ofNat (s + b))
      · have hcut :
            b = 3 ∧
              taoSection7SourceWhiteWCutoff n xi epsilon J j (Int.ofNat (s + b)) :=
          hW.mpr hraw
        rw [if_pos hcut, if_pos hraw]
        exact congrArg (fun t : ℕ => 1 + t) (ih (j + 1) (s + b) htail)
      · have hcut :
            ¬ (b = 3 ∧
              taoSection7SourceWhiteWCutoff n xi epsilon J j (Int.ofNat (s + b))) := by
          intro h
          exact hraw (hW.mp h)
        rw [if_neg hcut, if_neg hraw]
        exact congrArg (fun t : ℕ => 0 + t) (ih (j + 1) (s + b) htail)

/-- The finite source count is unchanged by cutoff gating before the cutoff. -/
theorem taoSection7WhiteHitCount_cutoff_eq
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) (J : ℕ)
    (bs : List ℕ) (hbs : bs.length ≤ J) :
    taoSection7WhiteHitCount
        (taoSection7SourceWhiteWCutoff n xi epsilon J) bs =
      taoSection7WhiteHitCount (taoSection7SourceWhiteW n xi epsilon) bs := by
  exact taoSection7WhiteHitCountFrom_cutoff_eq n xi epsilon J 1 0 bs (by omega)

end Tao
end Erdos1135
