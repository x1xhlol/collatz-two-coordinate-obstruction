import FiniteWindowAtoms

set_option autoImplicit false
open scoped BigOperators

namespace CollatzPassageAtoms
open Erdos1135.Tao CollatzClockAudit

noncomputable def firstPassageTimeTotal (B q : ℕ) : ℕ := by
  classical
  exact if hh : syracuseHitsAtMost q B then syracuseFirstPassageTime q B hh else 0

theorem firstPassageTimeTotal_of_first_hit {B q τ : ℕ}
    (hfirst : syracuseFirstHitAtMost B q τ) : firstPassageTimeTotal B q = τ := by
  classical
  have hh : syracuseHitsAtMost q B := ⟨τ, hfirst.1⟩
  rw [firstPassageTimeTotal, dif_pos hh]
  exact syracuseFirstHitAtMost_unique (syracuseFirstHitAtMost_of_hitsAtMost q B hh) hfirst

theorem total_passage_eq_iterate {B q : ℕ} (hB : 1 ≤ B)
    (hh : syracuseHitsAtMost q B) :
    (syracusePassLocationAtMostOrOne B q hB).val = (syracuse^[firstPassageTimeTotal B q]) q := by
  classical
  simp [firstPassageTimeTotal, hh]

noncomputable def boundedPassageWordEvent (B n L : ℕ) : Set ℕ :=
  {q | Odd q ∧ (∃ τ ≤ n, syracuseFirstHitAtMost B q τ) ∧
    (stoppedValuationWord (firstPassageTimeTotal B) q).sum ≤ L}

theorem prefix_good_bounded_word {B n q : ℕ} (hq : Odd q) {E : ℝ} (hE : 0 ≤ E)
    (hprefix : (⟨q, hq⟩ : TaoOddNat) ∈ actualPrefixGoodEvent n E)
    (hhit : ∃ τ ≤ n, syracuseFirstHitAtMost B q τ) :
    q ∈ boundedPassageWordEvent B n ⌊2 * (n : ℝ) + E⌋₊ := by
  obtain ⟨τ, hτ, hfirst⟩ := hhit
  refine ⟨hq, ⟨τ, hτ, hfirst⟩, ?_⟩
  rw [stoppedValuationWord_weight _ hq, firstPassageTimeTotal_of_first_hit hfirst]
  apply (Nat.le_floor_iff (by positivity : 0 ≤ 2 * (n : ℝ) + E)).mpr
  have hb := (abs_le.mp (hprefix τ hτ)).2
  have hτr : (τ : ℝ) ≤ n := by exact_mod_cast hτ
  dsimp at hb
  linarith

/-- The totalized landing atom is bounded by the bad-prefix probability plus
the complete stopped-word counting budget, including no-hit outcomes. -/
theorem total_passage_atom_probability_le {B lo hi n L : ℕ} (hB : 1 ≤ B)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (hsource : ∀ q ∈ oddLogWindow lo hi, B ≤ q) (m : ℕ) :
    ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure
      {q : TaoOddNat | (syracusePassLocationAtMostOrOne B q.1 hB).val = m}).toReal ≤
      ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure
        {q : TaoOddNat | q.1 ∉ boundedPassageWordEvent B n L}).toReal +
      (2 : ℝ) ^ L * ((1 : ℝ) / B / logFinsetMass (oddLogWindow lo hi)) := by
  let A : Set ℕ := {q | (syracusePassLocationAtMostOrOne B q hB).val = m}
  let G := boundedPassageWordEvent B n L
  change ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure {q : TaoOddNat | q.1 ∈ A}).toReal ≤ _
  rw [odd_window_nat_event_probability]
  have hbad : ((oddLogWindowOddNatPMF lo hi hmass).toOuterMeasure
      {q : TaoOddNat | q.1 ∉ boundedPassageWordEvent B n L}).toReal =
      logFinsetProb (oddLogWindow lo hi) Gᶜ := odd_window_nat_event_probability hmass Gᶜ
  rw [hbad]
  apply (logFinsetProb_split_le (oddLogWindow lo hi) A G).trans
  apply add_le_add le_rfl
  apply logFinsetProb_stopped_endpoint_le (oddLogWindow lo hi) (A ∩ G)
    (firstPassageTimeTotal B) L m B (by omega) hmass
  · intro q _ hq
    exact hq.2.1
  · intro q hq _
    exact hsource q hq
  · intro q _ hq
    exact hq.2.2.2
  · intro q _ hq
    obtain ⟨τ, _, hfirst⟩ := hq.2.2.1
    have hh : syracuseHitsAtMost q B := ⟨τ, hfirst.1⟩
    rw [← total_passage_eq_iterate hB hh]
    exact hq.1

end CollatzPassageAtoms
