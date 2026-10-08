import SyracuseLogTrajectory
import Erdos1135.Tao.Section5.PassTimeLocalization

namespace CollatzClockAudit
open Erdos1135.Tao

noncomputable def clockCenter (B q : ℕ) : ℝ :=
  (Real.log (q : ℝ) - Real.log (B : ℝ)) / clockDrift

noncomputable def clockRadius (E : ℝ) : ℝ :=
  (Real.log 2 * E + 1) / clockDrift + 1

noncomputable def clockUpperIndex (B q : ℕ) (E : ℝ) : ℕ :=
  ⌈clockCenter B q + (Real.log 2 * E + 1) / clockDrift⌉₊

theorem clockRadius_le_five {E : ℝ} (hE : 0 ≤ E) :
    clockRadius E ≤ 5 * (E + 1) := by
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hdiv : (Real.log 2 * E + 1) / clockDrift ≤ 4 * (E + 1) := by
    apply (div_le_iff₀ clockDrift_pos).2
    have hmul := mul_nonneg (sub_nonneg.mpr clockDrift_ge_quarter) hE
    have he := mul_le_mul_of_nonneg_right hlog hE
    nlinarith [clockDrift_ge_quarter]
  unfold clockRadius
  linarith

/-- Full-prefix valuation control yields a hit near the individual starting
point's logarithmic clock. The upper bracket is the only horizon assumption. -/
theorem exists_centered_first_hit {B q n0 : ℕ} {E : ℝ}
    (hB : 0 < B) (hq : Odd q) (hBq : B ≤ q) (hE : 0 ≤ E)
    (hcost : (n0 : ℝ) / (3 * B) ≤ 1)
    (htyp : ∀ j ≤ n0,
      |(taoTupleWeight (syracuseValuationPNatList j q hq) : ℝ) - 2 * j| ≤ E)
    (hupper : clockUpperIndex B q E ≤ n0) :
    ∃ τ ≤ n0, syracuseFirstHitAtMost B q τ ∧
      |(τ : ℝ) - clockCenter B q| ≤ clockRadius E := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hqpos : 0 < q := lt_of_lt_of_le hB hBq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hc : 0 ≤ clockCenter B q := by
    apply div_nonneg _ clockDrift_pos.le
    exact sub_nonneg.mpr (Real.log_le_log hBR (by exact_mod_cast hBq))
  let j := clockUpperIndex B q E
  have hj : j ≤ n0 := hupper
  have hround : clockCenter B q + (Real.log 2 * E + 1) / clockDrift ≤ (j : ℝ) :=
    Nat.le_ceil _
  have hcenter : clockCenter B q * clockDrift = Real.log (q : ℝ) - Real.log (B : ℝ) :=
    div_mul_cancel₀ _ clockDrift_pos.ne'
  have hmargin : ((Real.log 2 * E + 1) / clockDrift) * clockDrift = Real.log 2 * E + 1 :=
    div_mul_cancel₀ _ clockDrift_pos.ne'
  have hcross : ∃ k ≤ j, (syracuse^[k]) q ≤ B := by
    by_contra hn
    push Not at hn
    have hpre : ∀ i < j, B < (syracuse^[i]) q := fun i hi => hn i hi.le
    have hu := syracuse_log_upper_before_hit hB hq (htyp j hj) hpre
    have hcostj : (j : ℝ) / (3 * B) ≤ 1 := by
      apply le_trans _ hcost
      exact div_le_div_of_nonneg_right (by exact_mod_cast hj) (by positivity)
    have hscaled := mul_le_mul_of_nonneg_right hround clockDrift_pos.le
    have hloggt : Real.log (B : ℝ) < Real.log ((syracuse^[j]) q : ℝ) :=
      Real.log_lt_log hBR (by exact_mod_cast hn j le_rfl)
    nlinarith
  obtain ⟨k, hkj, hk⟩ := hcross
  have hh : syracuseHitsAtMost q B := ⟨k, hk⟩
  let τ := syracuseFirstPassageTime q B hh
  have hfirst : syracuseFirstHitAtMost B q τ := syracuseFirstHitAtMost_of_hitsAtMost q B hh
  have htj : τ ≤ j := by
    have htk : τ ≤ k := Nat.find_le hk
    exact htk.trans hkj
  have htn : τ ≤ n0 := htj.trans hj
  refine ⟨τ, htn, hfirst, ?_⟩
  have hlower := syracuse_log_lower_of_typical hq (htyp τ htn)
  have hloghit : Real.log ((syracuse^[τ]) q : ℝ) ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by exact_mod_cast syracuse_iterate_pos_clock hqpos τ)
      (by exact_mod_cast hfirst.1)
  have hleft : clockCenter B q - (Real.log 2 * E) / clockDrift ≤ (τ : ℝ) := by
    have hmul : ((Real.log 2 * E) / clockDrift) * clockDrift = Real.log 2 * E :=
      div_mul_cancel₀ _ clockDrift_pos.ne'
    apply (le_of_mul_le_mul_right ?_ clockDrift_pos)
    nlinarith
  have hx : 0 ≤ clockCenter B q + (Real.log 2 * E + 1) / clockDrift := by
    have hd := clockDrift_pos
    positivity
  have hceil : (j : ℝ) < clockCenter B q + (Real.log 2 * E + 1) / clockDrift + 1 :=
    Nat.ceil_lt_add_one hx
  have hright : (τ : ℝ) - clockCenter B q ≤ clockRadius E := by
    have hcast : (τ : ℝ) ≤ j := by exact_mod_cast htj
    unfold clockRadius
    linarith
  apply abs_le.mpr
  refine ⟨?_, hright⟩
  have hdiv : (Real.log 2 * E) / clockDrift ≤ (Real.log 2 * E + 1) / clockDrift :=
    div_le_div_of_nonneg_right (by linarith) clockDrift_pos.le
  unfold clockRadius
  linarith

theorem exists_centered_first_hit_five {B q n0 : ℕ} {E : ℝ}
    (hB : 0 < B) (hq : Odd q) (hBq : B ≤ q) (hE : 0 ≤ E)
    (hcost : (n0 : ℝ) / (3 * B) ≤ 1)
    (htyp : ∀ j ≤ n0,
      |(taoTupleWeight (syracuseValuationPNatList j q hq) : ℝ) - 2 * j| ≤ E)
    (hupper : clockUpperIndex B q E ≤ n0) :
    ∃ τ ≤ n0, syracuseFirstHitAtMost B q τ ∧
      |(τ : ℝ) - clockCenter B q| ≤ 5 * (E + 1) := by
  obtain ⟨τ, ht, hf, he⟩ := exists_centered_first_hit hB hq hBq hE hcost htyp hupper
  exact ⟨τ, ht, hf, he.trans (clockRadius_le_five hE)⟩

/-- The existing closed Section 5 prefix event directly supplies the
hypothesis of the individual centered clock theorem. -/
theorem section5_centered_first_hit {B q : ℕ}
    (hB : 0 < B) (hq : Odd q) (hBq : B ≤ q)
    (hcost : (taoSection5N0 B : ℝ) / (3 * B) ≤ 1)
    (htyp : taoSection5TypicalTuple B (taoSection5N0 B)
      (syracuseValuationPNatList (taoSection5N0 B) q hq))
    (hupper : clockUpperIndex B q (taoSection5TypicalSlack B) ≤ taoSection5N0 B) :
    ∃ τ ≤ taoSection5N0 B, syracuseFirstHitAtMost B q τ ∧
      |(τ : ℝ) - clockCenter B q| ≤ 5 * (taoSection5TypicalSlack B + 1) := by
  have hE : 0 ≤ taoSection5TypicalSlack B := by
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hB)) _
  apply exists_centered_first_hit_five hB hq hBq hE hcost _ hupper
  intro j hj
  have hb := TaoSection5TypicalTuple.actual_prefix_weight_bounds hq htyp hj
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

end CollatzClockAudit

#print axioms CollatzClockAudit.clockRadius_le_five
#print axioms CollatzClockAudit.exists_centered_first_hit
#print axioms CollatzClockAudit.exists_centered_first_hit_five
#print axioms CollatzClockAudit.section5_centered_first_hit
