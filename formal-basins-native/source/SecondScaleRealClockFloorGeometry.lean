import SecondScaleRealClockSourceTransport

namespace CollatzClockSecondScale
open Erdos1135SecondScale.Tao

def realLocalClockGoodEvent (x : ℝ) : Set TaoOddNat :=
  {q | ∃ τ, syracuseFirstHitAtMostReal x q.1 τ ∧
    |(τ : ℝ) - (Real.log (q.1 : ℝ) - Real.log x) / clockDrift| ≤
      20 * (Real.log x) ^ (3 / 5 : ℝ)}

def realLargeLandingGoodEvent (x : ℝ) : Set TaoOddNat :=
  {q | ∃ τ, syracuseFirstHitAtMostReal x q.1 τ ∧
    x ^ (1 / 2 : ℝ) < ((syracuse^[τ]) q.1 : ℝ)}

theorem real_floor_log_gap {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ Real.log x - Real.log ((Nat.floor x : ℕ) : ℝ) ∧
      Real.log x - Real.log ((Nat.floor x : ℕ) : ℝ) ≤ 1 := by
  have hxpos : 0 < x := by linarith
  have hB : 1 ≤ Nat.floor x := Nat.le_floor (by norm_num; linarith)
  have hBR : (0 : ℝ) < Nat.floor x := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ Nat.floor x := by exact_mod_cast hB
  have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hup := Nat.lt_floor_add_one x
  have hx2 : x ≤ 2 * ((Nat.floor x : ℕ) : ℝ) := by linarith
  have hlo := Real.log_le_log hBR hfloor
  have hhi := Real.log_le_log hxpos hx2
  rw [Real.log_mul (by norm_num) hBR.ne'] at hhi
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  constructor <;> linarith

theorem half_log_le_log_floor {x : ℝ} (hx : 2 ≤ x) (hlog : 2 ≤ Real.log x) :
    Real.log x / 2 ≤ Real.log ((Nat.floor x : ℕ) : ℝ) := by
  have h := real_floor_log_gap hx
  linarith

theorem localClockGoodEvent_floor_subset_real {x : ℝ} (hx : 2 ≤ x)
    (hlog : 1 ≤ Real.log x) :
    localClockGoodEvent (Nat.floor x) (taoSection5N0 (Nat.floor x))
      (taoSection5TypicalSlack (Nat.floor x)) ⊆ realLocalClockGoodEvent x := by
  intro q hq
  obtain ⟨τ, _, hfirst, herr⟩ := hq
  have hxpos : 0 < x := by linarith
  have hB : 1 ≤ Nat.floor x := Nat.le_floor (by norm_num; linarith)
  have hBR : (0 : ℝ) < Nat.floor x := by exact_mod_cast hB
  have hLB : 0 ≤ Real.log ((Nat.floor x : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hB)
  have hgap := real_floor_log_gap hx
  have hE : taoSection5TypicalSlack (Nat.floor x) ≤ (Real.log x) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow hLB (by linarith [hgap.1]) (by norm_num)
  have hEone : 1 ≤ (Real.log x) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow hlog (by norm_num)
  have hshift : |clockCenter (Nat.floor x) q.1 -
      (Real.log (q.1 : ℝ) - Real.log x) / clockDrift| ≤ 4 := by
    have hid : clockCenter (Nat.floor x) q.1 -
        (Real.log (q.1 : ℝ) - Real.log x) / clockDrift =
          (Real.log x - Real.log ((Nat.floor x : ℕ) : ℝ)) / clockDrift := by
      unfold clockCenter
      ring
    rw [hid, abs_of_nonneg (div_nonneg hgap.1 clockDrift_pos.le)]
    apply (div_le_iff₀ clockDrift_pos).2
    nlinarith [clockDrift_ge_quarter]
  refine ⟨τ, (syracuseFirstHitAtMostReal_iff_floor hxpos.le).2 hfirst, ?_⟩
  have htriangle := abs_sub_le (τ : ℝ) (clockCenter (Nat.floor x) q.1)
    ((Real.log (q.1 : ℝ) - Real.log x) / clockDrift)
  linarith

/-- The stronger logarithmic landing estimate also survives the floor
change, giving the paper's actual `sqrt x` landing scale. -/
theorem real_landing_gt_sqrt_of_coarse_prefix {x : ℝ} {q n0 τ : ℕ}
    (hx : 2 ≤ x) (hlog : 100 ≤ Real.log ((Nat.floor x : ℕ) : ℝ))
    (hq : Odd q) (hτ : 0 < τ) (hτn : τ ≤ n0)
    (hfirst : syracuseFirstHitAtMost (Nat.floor x) q τ)
    (htyp : ∀ j ≤ n0,
      |(taoTupleWeight (syracuseValuationPNatList j q hq) : ℝ) - 2 * j| ≤
        Real.log ((Nat.floor x : ℕ) : ℝ) / 1000) :
    x ^ (1 / 2 : ℝ) < ((syracuse^[τ]) q : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hB : 0 < Nat.floor x := Nat.le_floor (by norm_num; linarith)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hτ.ne'
  have hlower := first_hit_log_landing_lower hB hq hfirst (htyp r (by omega))
    (by simpa only [Nat.cast_add, Nat.cast_one] using htyp (r + 1) hτn)
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hl2
    (show 0 ≤ 2 + 2 * (Real.log ((Nat.floor x : ℕ) : ℝ) / 1000) by linarith)
  have hgap := real_floor_log_gap hx
  have hlogY : (1 / 2 : ℝ) * Real.log x < Real.log ((syracuse^[r + 1]) q : ℝ) := by
    nlinarith
  have hqpos : 0 < q := by rcases hq with ⟨k, hk⟩; omega
  have hypos : (0 : ℝ) < (syracuse^[r + 1]) q := by
    exact_mod_cast syracuse_iterate_pos_clock hqpos (r + 1)
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hxpos _) hypos).mp
  rwa [Real.log_rpow hxpos]

end CollatzClockSecondScale

#print axioms CollatzClockSecondScale.real_floor_log_gap
#print axioms CollatzClockSecondScale.half_log_le_log_floor
#print axioms CollatzClockSecondScale.localClockGoodEvent_floor_subset_real
#print axioms CollatzClockSecondScale.real_landing_gt_sqrt_of_coarse_prefix
