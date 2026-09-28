import Erdos1135.Tao.Renewal.Prop78CanonicalAssembly

/-!
# Zero-Safe Qm Induction and Pointwise (7.37)

This leaf extends the positive-index `Q_m ≤ m^A` estimate to the totalized
zero index through `max m 1`, consumes canonical Proposition 7.8 by strong
induction, and evaluates the full cutoff supremum to obtain pointwise decay.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- The supplied-`Q` supremum inherits the zero-safe pointwise
`max(m,1)^A` bound. -/
theorem taoSection7SourceQm_le_max_pow_of_bounded01
    {J A m : ℕ} {Q : TaoSection7Q}
    (hQ : TaoSection7QBounded01 Q) :
    taoSection7SourceQm J A Q m ≤
      ((max m 1 : ℕ) : ℝ) ^ A := by
  unfold taoSection7SourceQm
  exact csSup_le
    (taoSection7QmValueSet_nonempty J A Q m)
    (by
      intro x hx
      rcases hx with ⟨p, hp, rfl⟩
      exact taoSection7QmWeightedValue_le_max_pow_of_bounded01
        (J := J) (A := A) (m := m) (Q := Q) hQ hp)

/-- Zero-safe source-actual cutoff bound, including `m = 0`. -/
theorem taoSection7SourceActualQmAtCutoff_le_max_pow
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
      ((max m 1 : ℕ) : ℝ) ^ A := by
  unfold taoSection7SourceActualQmAtCutoff taoSection7SourceActualQm
  exact taoSection7SourceQm_le_max_pow_of_bounded01
    (J := n / 2) (A := A) (m := m)
    (Q := taoSection7SourceActualQ n xi epsilon)
    (taoSection7SourceActualQ_bounded01
      (n := n) (xi := xi) hepsilon)

/-- Evaluate the actual weighted value at any point of the cutoff tail. -/
theorem taoSection7SourceActualQ_weighted_le_QmAtCutoff
    {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    {p : TaoSection7RenewalPoint}
    (hp : taoSection7QmTail (n / 2) m p) :
    (taoSection7QDistanceToCutoff (n / 2) p : ℝ) ^ A *
        taoSection7SourceActualQ n xi epsilon p ≤
      taoSection7SourceActualQmAtCutoff n A m xi epsilon := by
  have hbdd := taoSection7QmValueSet_bddAbove_of_bounded01
    (J := n / 2) (A := A) (m := m)
    (Q := taoSection7SourceActualQ n xi epsilon)
    (taoSection7SourceActualQ_bounded01
      (n := n) (xi := xi) hepsilon)
  have hweighted := taoSection7QmWeightedValue_le_sourceQm
    (J := n / 2) (A := A) (k := m)
    (Q := taoSection7SourceActualQ n xi epsilon) hbdd hp
  simpa [taoSection7QmWeightedValue,
    taoSection7SourceActualQmAtCutoff,
    taoSection7SourceActualQm] using hweighted

/-- Strong-induction consumer for a thresholded Proposition 7.8
monotonicity theorem.  The `m ≤ C` branch uses the zero-safe base bound. -/
theorem
    taoSection7SourceActualQmAtCutoff_le_threshold_pow_of_monotonicity
    {n A C : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hC : TaoSection7Prop78Threshold A epsilon C)
    (hmono : ∀ m : ℕ, C ≤ m → m ≤ n / 2 →
      taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
        taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon) :
    ∀ m : ℕ, m ≤ n / 2 →
      taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
        (C : ℝ) ^ A := by
  have honeC : 1 ≤ C := by
    simpa [taoSection7Prop78LowerThreshold] using hC.lowerThreshold_le
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm_hi
      by_cases hmC : m ≤ C
      · have hmaxC : max m 1 ≤ C := max_le hmC honeC
        calc
          taoSection7SourceActualQmAtCutoff n A m xi epsilon ≤
              ((max m 1 : ℕ) : ℝ) ^ A :=
            taoSection7SourceActualQmAtCutoff_le_max_pow hepsilon
          _ ≤ (C : ℝ) ^ A :=
            pow_le_pow_left₀ (Nat.cast_nonneg _)
              (Nat.cast_le.mpr hmaxC) A
      · have hCm : C ≤ m := by omega
        exact
          (hmono m hCm hm_hi).trans
            (ih (m - 1) (by omega) (by omega))

/-- Canonical Proposition 7.8 controls every totalized cutoff supremum by one
threshold power, uniformly in the ambient primitive frequency. -/
theorem exists_taoSection7Prop78_canonical_Qm_le_threshold_pow
    (packet : TaoSection7Prop78AbsolutePacket)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℕ,
      TaoSection7Prop78Threshold A packet.epsilon C ∧
      ∀ (n : ℕ) (xi : ZMod (3 ^ n))
        (hxi : zmodThreePrimitive n xi) (m : ℕ),
        m ≤ n / 2 →
        taoSection7SourceActualQmAtCutoff
            n A m xi packet.epsilon ≤
          (C : ℝ) ^ A := by
  obtain ⟨C, hC, hmono⟩ :=
    exists_taoSection7Prop78_canonical_monotonicity_740_threshold
      packet A hA
  refine ⟨C, hC, ?_⟩
  intro n xi hxi m hm_hi
  exact
    taoSection7SourceActualQmAtCutoff_le_threshold_pow_of_monotonicity
      packet.scalar.epsilon_pos.le hC
      (fun k hkC hk_hi => hmono n xi hxi k hkC hk_hi)
      m hm_hi

/-- Full-cutoff pointwise `(7.37)`, valid even when `n / 2 = 0`.  The only
division is by the positive source distance power. -/
theorem exists_taoSection7Prop78_canonical_pointwise_737
    (packet : TaoSection7Prop78AbsolutePacket)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℕ,
      TaoSection7Prop78Threshold A packet.epsilon C ∧
      ∀ (n : ℕ) (xi : ZMod (3 ^ n))
        (hxi : zmodThreePrimitive n xi)
        (p : TaoSection7RenewalPoint),
        taoSection7SourceActualQ n xi packet.epsilon p ≤
          (C : ℝ) ^ A *
            (((taoSection7QDistanceToCutoff (n / 2) p : ℝ) ^ A)⁻¹) := by
  obtain ⟨C, hC, hQm⟩ :=
    exists_taoSection7Prop78_canonical_Qm_le_threshold_pow packet A hA
  refine ⟨C, hC, ?_⟩
  intro n xi hxi p
  have htail : taoSection7QmTail (n / 2) (n / 2) p := by
    unfold taoSection7QmTail
    omega
  have hweighted := taoSection7SourceActualQ_weighted_le_QmAtCutoff
    (n := n) (A := A) (m := n / 2) (xi := xi)
    packet.scalar.epsilon_pos.le htail
  have hprod :
      (taoSection7QDistanceToCutoff (n / 2) p : ℝ) ^ A *
          taoSection7SourceActualQ n xi packet.epsilon p ≤
        (C : ℝ) ^ A :=
    hweighted.trans (hQm n xi hxi (n / 2) le_rfl)
  let d : ℕ := taoSection7QDistanceToCutoff (n / 2) p
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one
        (le_max_right (n / 2 - (p.j : ℕ)) 1))
  have hpow_pos : 0 < (d : ℝ) ^ A := pow_pos hd A
  have hpow_ne : (d : ℝ) ^ A ≠ 0 := ne_of_gt hpow_pos
  change taoSection7SourceActualQ n xi packet.epsilon p ≤
    (C : ℝ) ^ A * (((d : ℝ) ^ A)⁻¹)
  change (d : ℝ) ^ A *
      taoSection7SourceActualQ n xi packet.epsilon p ≤
    (C : ℝ) ^ A at hprod
  calc
    taoSection7SourceActualQ n xi packet.epsilon p =
        (((d : ℝ) ^ A)⁻¹) *
          ((d : ℝ) ^ A *
            taoSection7SourceActualQ n xi packet.epsilon p) := by
      field_simp [hpow_ne]
    _ ≤ (((d : ℝ) ^ A)⁻¹) * (C : ℝ) ^ A :=
      mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hpow_pos.le)
    _ = (C : ℝ) ^ A * (((d : ℝ) ^ A)⁻¹) := by ring

end

end Tao
end Erdos1135
