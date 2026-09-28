import SyracuseCenteredPassage

namespace CollatzClockAudit
open Erdos1135.Tao

/-- Two adjacent prefix deviations bound the single valuation between them. -/
theorem terminal_valuation_le_of_prefix_bounds {q r : ℕ} (hq : Odd q) {E : ℝ}
    (hprev : |(taoTupleWeight (syracuseValuationPNatList r q hq) : ℝ) - 2 * r| ≤ E)
    (hnext : |(taoTupleWeight (syracuseValuationPNatList (r + 1) q hq) : ℝ) - 2 * (r + 1)| ≤ E) :
    (syracuseExponent ((syracuse^[r]) q) : ℝ) ≤ 2 + 2 * E := by
  rw [taoTupleWeight_syracuseValuationPNatList_succ] at hnext
  simp only [Nat.cast_add, syracuseTerminalExponentPNat, PNat.mk_coe] at hnext
  have hp := (abs_le.mp hprev).1
  have hn := (abs_le.mp hnext).2
  linarith

/-- A positive-time first hit cannot land too far below its barrier when
adjacent valuation sums are controlled. -/
theorem first_hit_log_landing_lower {B q r : ℕ} (hB : 0 < B) (hq : Odd q) {E : ℝ}
    (hfirst : syracuseFirstHitAtMost B q (r + 1))
    (hprev : |(taoTupleWeight (syracuseValuationPNatList r q hq) : ℝ) - 2 * r| ≤ E)
    (hnext : |(taoTupleWeight (syracuseValuationPNatList (r + 1) q hq) : ℝ) - 2 * (r + 1)| ≤ E) :
    Real.log (B : ℝ) + Real.log 3 - (2 + 2 * E) * Real.log 2 <
      Real.log ((syracuse^[r + 1]) q : ℝ) := by
  have hpre : B < (syracuse^[r]) q := hfirst.2 r (by omega)
  have hp : 0 < (syracuse^[r]) q := lt_trans hB hpre
  have hpR : (0 : ℝ) < (syracuse^[r]) q := by exact_mod_cast hp
  have hlogpre : Real.log (B : ℝ) < Real.log ((syracuse^[r]) q : ℝ) :=
    Real.log_lt_log (by exact_mod_cast hB) (by exact_mod_cast hpre)
  have hv := terminal_valuation_le_of_prefix_bounds hq hprev hnext
  have hl2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hcorr : 0 ≤ Real.log (1 + 1 / (3 * ((syracuse^[r]) q : ℝ))) := by
    apply Real.log_nonneg
    have hx : 0 ≤ (1 : ℝ) / (3 * ((syracuse^[r]) q : ℝ)) := by positivity
    linarith
  rw [Function.iterate_succ_apply', syracuse_log_step hp]
  nlinarith

/-- The coarse event with error at most `log B / 1000` keeps the landing
above `sqrt B`, once `log B ≥ 100`. -/
theorem first_hit_landing_gt_sqrt_of_prefix_bounds {B q n0 τ : ℕ}
    (hB : 0 < B) (hq : Odd q) (hτ : 0 < τ) (hτn : τ ≤ n0) {E : ℝ}
    (hE : 0 ≤ E) (hElog : E ≤ Real.log (B : ℝ) / 1000)
    (hlogB : 100 ≤ Real.log (B : ℝ))
    (hfirst : syracuseFirstHitAtMost B q τ)
    (htyp : ∀ j ≤ n0,
      |(taoTupleWeight (syracuseValuationPNatList j q hq) : ℝ) - 2 * j| ≤ E) :
    (B : ℝ) ^ (1 / 2 : ℝ) < ((syracuse^[τ]) q : ℝ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hτ.ne'
  have hprev := htyp r (by omega)
  have hnext := htyp (r + 1) hτn
  have hlower := first_hit_log_landing_lower hB hq hfirst hprev
    (by simpa only [Nat.cast_add, Nat.cast_one] using hnext)
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hl2 (show 0 ≤ 2 + 2 * E by linarith)
  have hlog : (1 / 2 : ℝ) * Real.log (B : ℝ) < Real.log ((syracuse^[r + 1]) q : ℝ) := by
    nlinarith
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hqpos : 0 < q := by rcases hq with ⟨k, hk⟩; omega
  have hy : (0 : ℝ) < (syracuse^[r + 1]) q := by
    exact_mod_cast syracuse_iterate_pos_clock hqpos (r + 1)
  have hx : (0 : ℝ) < (B : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hBR _
  have hl : Real.log ((B : ℝ) ^ (1 / 2 : ℝ)) < Real.log ((syracuse^[r + 1]) q : ℝ) := by
    rwa [Real.log_rpow hBR]
  exact (Real.log_lt_log_iff hx hy).mp hl

end CollatzClockAudit

#print axioms CollatzClockAudit.terminal_valuation_le_of_prefix_bounds
#print axioms CollatzClockAudit.first_hit_log_landing_lower
#print axioms CollatzClockAudit.first_hit_landing_gt_sqrt_of_prefix_bounds
