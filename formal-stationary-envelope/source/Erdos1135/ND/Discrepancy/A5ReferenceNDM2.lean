import Erdos1135.ND.Statement
import Erdos1135.ND.Discrepancy.A5ReferenceRealFloorPass

/-!
# Same-exponent ND-M2 facade

This leaf converts the checked raw real-source A5 rows to the frozen ND-M2
surface.  The hit exponent remains the independent power `1 / 32000`; the
transport exponent is exactly the same symbolic `d` consumed downstream.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

private theorem ndM2_half_le_natFloor_cast
    {x : Real} (hx : 2 <= x) :
    x / 2 <= ((Nat.floor x : Nat) : Real) := by
  have hfloor := Nat.lt_floor_add_one x
  nlinarith

private theorem ndM2_half_log_le_log_natFloor_cast
    {x : Real} (hx : 2 <= x) (hlog : 2 <= Real.log x) :
    Real.log x / 2 <= Real.log ((Nat.floor x : Nat) : Real) := by
  have hxpos : 0 < x := by linarith
  have hxhalfPos : 0 < x / 2 := div_pos hxpos (by norm_num)
  have hhalf := ndM2_half_le_natFloor_cast hx
  have hfloorPos : 0 < ((Nat.floor x : Nat) : Real) :=
    hxhalfPos.trans_le hhalf
  have hmono :=
    Real.strictMonoOn_log.monotoneOn hxhalfPos hfloorPos hhalf
  rw [Real.log_div hxpos.ne' (by norm_num : (2 : Real) ≠ 0)] at hmono
  have hlogTwo : Real.log (2 : Real) < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : Real) < 2 by norm_num)
      (show (2 : Real) ≠ 1 by norm_num)
    norm_num at h
    exact h
  linarith

private theorem ndM2_rpow_neg_le_two_rpow_mul_of_half_le
    {a b c e : Real} (ha : 0 < a) (haOne : 1 <= a)
    (hab : a / 2 <= b) (hc : 0 <= c) (hec : e <= c) :
    b ^ (-c) <= (2 : Real) ^ c * a ^ (-e) := by
  have hhalfPos : 0 < a / 2 := div_pos ha (by norm_num)
  have hbase : b ^ (-c) <= (a / 2) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos hhalfPos hab (neg_nonpos.mpr hc)
  have hfactor : (a / 2) ^ (-c) = (2 : Real) ^ c * a ^ (-c) := by
    rw [Real.div_rpow ha.le (by norm_num : (0 : Real) <= 2),
      Real.rpow_neg (by norm_num : (0 : Real) <= 2)]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  have hexponent : a ^ (-c) <= a ^ (-e) :=
    Real.rpow_le_rpow_of_exponent_le haOne (neg_le_neg hec)
  calc
    b ^ (-c) <= (a / 2) ^ (-c) := hbase
    _ = (2 : Real) ^ c * a ^ (-c) := hfactor
    _ <= (2 : Real) ^ c * a ^ (-e) :=
      mul_le_mul_of_nonneg_left hexponent
        (Real.rpow_nonneg (by norm_num) _)

private theorem ndM2_deltaH_floor_le_inv_x
    {x : Real} (hx : 2 <= x)
    (hlogFloor : 1 <= Real.log ((Nat.floor x : Nat) : Real)) :
    96000 /
        (((Nat.floor x : Nat) : Real) *
          Real.log ((Nat.floor x : Nat) : Real)) <=
      192000 / x := by
  have hxpos : 0 < x := by linarith
  have hhalf := ndM2_half_le_natFloor_cast hx
  have hfloorNonneg : 0 <= ((Nat.floor x : Nat) : Real) :=
    Nat.cast_nonneg _
  have hfloorLeProd : ((Nat.floor x : Nat) : Real) <=
      ((Nat.floor x : Nat) : Real) *
        Real.log ((Nat.floor x : Nat) : Real) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlogFloor hfloorNonneg
  have hden : x / 2 <=
      ((Nat.floor x : Nat) : Real) *
        Real.log ((Nat.floor x : Nat) : Real) :=
    hhalf.trans hfloorLeProd
  calc
    96000 /
          (((Nat.floor x : Nat) : Real) *
            Real.log ((Nat.floor x : Nat) : Real)) <=
        96000 / (x / 2) :=
      div_le_div_of_nonneg_left (by norm_num)
        (div_pos hxpos (by norm_num)) hden
    _ = 192000 / x := by
      field_simp [hxpos.ne']
      norm_num

/-- The raw real-source A5 rows have the exact two rates consumed by ND-M2.
The same witnesses simultaneously carry the uniform escape and full-L1
passage bounds for both source branches. -/
theorem eventually_ndA5RealSameBranchRateBounds
    {c kappa d : Real} (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ x : Real in atTop,
      ∀ (hx : 1 <= x) (branch : Tao.TaoSection5SourceBranch),
        let y := transportSourceY x branch
        ∃ hwindow : (oddBlock y).Nonempty,
        ∃ hmass : 0 < Tao.logFinsetMass (oddBlock y),
          uniformNoHitProbability x y hwindow <=
              184 * x ^ (-(1 / 32000 : Real)) ∧
            passFullL1 x y hx hwindow hmass <=
              384256 * (Real.log x) ^ (-d) := by
  have hdOne : d <= 1 := by linarith [hd20]
  filter_upwards
      [eventually_ndA5RealSameBranchRawBounds
        hPhase hd hd20 hdk,
        eventually_ge_atTop (2 : Real),
        Real.tendsto_log_atTop.eventually_ge_atTop (2 : Real)]
      with x hraw hxTwo hlog
  ·
    intro hx branch
    rcases hraw hx branch with
      ⟨hwindow, hmass, hhitRaw, hpassRaw⟩
    have hxpos : 0 < x := by linarith
    have hhalf := ndM2_half_le_natFloor_cast hxTwo
    have hfloorPowBase :
        ((Nat.floor x : Nat) : Real) ^ (-(1 / 32000 : Real)) <=
          (2 : Real) ^ (1 / 32000 : Real) *
            x ^ (-(1 / 32000 : Real)) :=
      ndM2_rpow_neg_le_two_rpow_mul_of_half_le
        hxpos hx hhalf (by norm_num) (le_refl _)
    have htwoHit : (2 : Real) ^ (1 / 32000 : Real) <= 2 := by
      calc
        (2 : Real) ^ (1 / 32000 : Real) <= (2 : Real) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := by norm_num
    have hfloorPow :
        ((Nat.floor x : Nat) : Real) ^ (-(1 / 32000 : Real)) <=
          2 * x ^ (-(1 / 32000 : Real)) :=
      hfloorPowBase.trans
        (mul_le_mul_of_nonneg_right htwoHit
          (Real.rpow_nonneg hxpos.le _))
    have hpolyHit :
        x ^ (-(99 / 100 : Real)) <=
          x ^ (-(1 / 32000 : Real)) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    have hhit :
        uniformNoHitProbability x (transportSourceY x branch) hwindow <=
          184 * x ^ (-(1 / 32000 : Real)) := by
      calc
        _ <= 44 * ((Nat.floor x : Nat) : Real) ^
              (-(1 / 32000 : Real)) +
            96 * x ^ (-(99 / 100 : Real)) := hhitRaw
        _ <= 44 * (2 * x ^ (-(1 / 32000 : Real))) +
            96 * x ^ (-(1 / 32000 : Real)) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hfloorPow (by norm_num))
            (mul_le_mul_of_nonneg_left hpolyHit (by norm_num))
        _ = 184 * x ^ (-(1 / 32000 : Real)) := by ring
    have hlogPos : 0 < Real.log x := by linarith
    have hlogOne : 1 <= Real.log x := by linarith
    have hlogHalf :=
      ndM2_half_log_le_log_natFloor_cast hxTwo hlog
    have hlogFloor :
        1 <= Real.log ((Nat.floor x : Nat) : Real) := by
      linarith
    have hfloorLogPowBase :
        Real.log ((Nat.floor x : Nat) : Real) ^ (-d) <=
          (2 : Real) ^ d * (Real.log x) ^ (-d) :=
      ndM2_rpow_neg_le_two_rpow_mul_of_half_le
        hlogPos hlogOne hlogHalf hd.le (le_refl _)
    have htwoD : (2 : Real) ^ d <= 2 := by
      calc
        (2 : Real) ^ d <= (2 : Real) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hdOne
        _ = 2 := by norm_num
    have hfloorLogPow :
        ndA5ReferenceInteriorScalarRate (Nat.floor x) d <=
          2 * (Real.log x) ^ (-d) := by
      unfold ndA5ReferenceInteriorScalarRate
      exact hfloorLogPowBase.trans
        (mul_le_mul_of_nonneg_right htwoD
          (Real.rpow_nonneg hlogPos.le _))
    have hlogLeX : Real.log x <= x := by
      have h := Real.log_le_sub_one_of_pos hxpos
      linarith
    have hxDToLog : x ^ (-d) <= (Real.log x) ^ (-d) :=
      Real.rpow_le_rpow_of_nonpos hlogPos hlogLeX
        (neg_nonpos.mpr hd.le)
    have hpolyD :
        x ^ (-(99 / 100 : Real)) <= (Real.log x) ^ (-d) := by
      exact (Real.rpow_le_rpow_of_exponent_le hx
        (by linarith [hd20])).trans hxDToLog
    have hinvToLog : 1 / x <= (Real.log x) ^ (-d) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact (Real.rpow_le_rpow_of_exponent_le hx
        (neg_le_neg hdOne)).trans hxDToLog
    have hdeltaBase := ndM2_deltaH_floor_le_inv_x hxTwo hlogFloor
    have hdelta :
        2 * (96000 /
            (((Nat.floor x : Nat) : Real) *
              Real.log ((Nat.floor x : Nat) : Real))) <=
          384000 * (Real.log x) ^ (-d) := by
      calc
        _ <= 2 * (192000 / x) :=
          mul_le_mul_of_nonneg_left hdeltaBase (by norm_num)
        _ = 384000 * (1 / x) := by ring
        _ <= 384000 * (Real.log x) ^ (-d) :=
          mul_le_mul_of_nonneg_left hinvToLog (by norm_num)
    have hpass :
        passFullL1 x (transportSourceY x branch) hx hwindow hmass <=
          384256 * (Real.log x) ^ (-d) := by
      calc
        _ <= 2 * (96 * x ^ (-(99 / 100 : Real))) +
              32 * ndA5ReferenceInteriorScalarRate (Nat.floor x) d +
                2 * (96000 /
                  (((Nat.floor x : Nat) : Real) *
                    Real.log ((Nat.floor x : Nat) : Real))) := hpassRaw
        _ <= 2 * (96 * (Real.log x) ^ (-d)) +
              32 * (2 * (Real.log x) ^ (-d)) +
                384000 * (Real.log x) ^ (-d) :=
          add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hpolyD (by norm_num))
                (by norm_num))
              (mul_le_mul_of_nonneg_left hfloorLogPow (by norm_num)))
            hdelta
        _ = 384256 * (Real.log x) ^ (-d) := by ring
    exact ⟨hwindow, hmass, hhit, hpass⟩

/-- The checked A5 real-source rows prove ND-M2 with hit exponent
`1 / 32000` and with transport exponent exactly the supplied `d`.
-/
theorem ndA5ReferenceNDM2Bounds_sameD
    {c kappa d : Real} (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    NDM2Bounds (1 / 32000 : Real) d := by
  rcases eventually_atTop.1
      (eventually_ndA5RealSameBranchRateBounds
        hPhase hd hd20 hdk) with ⟨x0, hx0⟩
  unfold NDM2Bounds
  refine ⟨184, 384256, max 2 x0, by norm_num, by norm_num,
    le_max_left _ _, ?_⟩
  intro x hxx hx branch
  exact hx0 x ((le_max_right (2 : Real) x0).trans hxx) hx branch

end
end ND
end Erdos1135
