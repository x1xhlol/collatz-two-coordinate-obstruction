import Erdos1135.Tao.Section5.PassSchedule
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# A5 common reference schedule

This leaf fixes the single reference level used by both low laws in the A5
scheduler.  It keeps the elementary floor and ceiling estimates below the
completed Tao Section 5 integration modules.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

private theorem eventually_log_div_two_hundred_thousand_le_ndA5M0 :
    ∀ᶠ B : ℕ in atTop,
      Real.log B / 200000 ≤ (Tao.taoSection5M0 B : ℝ) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (200000 : ℝ)] with B hlarge
  have hfloor :
      Real.log B / 100000 - 1 < (Tao.taoSection5M0 B : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.log B / 100000)
    rw [← Tao.taoSection5M0_eq_floor_log B] at h
    have h' :
        Real.log B / 100000 < (Tao.taoSection5M0 B : ℝ) + 1 := by
      exact_mod_cast h
    linarith
  nlinarith

private theorem ndA5M0_cast_le_log_div_hundred_thousand (B : ℕ) :
    (Tao.taoSection5M0 B : ℝ) ≤ Real.log B / 100000 := by
  rw [Tao.taoSection5M0_eq_floor_log]
  exact_mod_cast Nat.floor_le (by positivity : 0 ≤ Real.log B / 100000)

/-- The one literal fixed-time level shared by the harmonic and flat A5 laws. -/
noncomputable def ndA5ReferenceLevel (B : ℕ) : ℕ :=
  Nat.ceil ((Tao.taoSection5M0 B : ℝ) *
    Real.rpow (Real.log B) (-(2 / 5 : ℝ)))

/-- The reference level has the frozen `log(B)^(3/5)` scale, with the ceiling
error absorbed into the upper constant. -/
theorem eventually_ndA5ReferenceLevel_cast_sandwich :
    ∀ᶠ B : ℕ in atTop,
      (1 / 200000 : ℝ) * Real.rpow (Real.log B) (3 / 5 : ℝ) ≤
          (ndA5ReferenceLevel B : ℝ) ∧
      (ndA5ReferenceLevel B : ℝ) ≤
          (1 / 50000 : ℝ) * Real.rpow (Real.log B) (3 / 5 : ℝ) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (3 / 5 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop
      (by norm_num : (0 : ℝ) < 3 / 5)).comp hlog
  filter_upwards
    [eventually_log_div_two_hundred_thousand_le_ndA5M0,
      hlog.eventually_ge_atTop (1 : ℝ),
      hpow.eventually_ge_atTop (100000 : ℝ)]
      with B hm0Lower hlogOne hpowLarge
  let L : ℝ := Real.log B
  let s : ℝ := Real.rpow L (-(2 / 5 : ℝ))
  let R : ℝ := Real.rpow L (3 / 5 : ℝ)
  let x : ℝ := (Tao.taoSection5M0 B : ℝ) * s
  have hLpos : 0 < L := by
    dsimp only [L]
    exact zero_lt_one.trans_le hlogOne
  have hs0 : 0 ≤ s := by
    dsimp only [s]
    exact Real.rpow_nonneg hLpos.le _
  have hfactor : L * s = R := by
    calc
      L * s = Real.rpow L (1 : ℝ) * s := by
        congr 1
        exact (Real.rpow_one L).symm
      _ = Real.rpow L (1 : ℝ) * Real.rpow L (-(2 / 5 : ℝ)) := by
        rfl
      _ = Real.rpow L ((1 : ℝ) + (-(2 / 5 : ℝ))) :=
        (Real.rpow_add hLpos (1 : ℝ) (-(2 / 5 : ℝ))).symm
      _ = R := by norm_num [R]
  have hm0Upper :
      (Tao.taoSection5M0 B : ℝ) ≤ L / 100000 := by
    simpa only [L] using ndA5M0_cast_le_log_div_hundred_thousand B
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg (Nat.cast_nonneg _) hs0
  have hxLower : (L / 200000) * s ≤ x := by
    dsimp only [x]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [L] using hm0Lower) hs0
  have hxUpper : x ≤ (L / 100000) * s := by
    dsimp only [x]
    exact mul_le_mul_of_nonneg_right hm0Upper hs0
  have hscaledLower :
      (1 / 200000 : ℝ) * R ≤ x := by
    calc
      (1 / 200000 : ℝ) * R = (L / 200000) * s := by
        rw [← hfactor]
        ring
      _ ≤ x := hxLower
  have hscaledUpper :
      x ≤ (1 / 100000 : ℝ) * R := by
    calc
      x ≤ (L / 100000) * s := hxUpper
      _ = (1 / 100000 : ℝ) * R := by
        rw [← hfactor]
        ring
  have hceilLower :
      x ≤ (ndA5ReferenceLevel B : ℝ) := by
    simpa only [ndA5ReferenceLevel, x] using Nat.le_ceil x
  have hceilUpper :
      (ndA5ReferenceLevel B : ℝ) < x + 1 := by
    simpa only [ndA5ReferenceLevel, x] using Nat.ceil_lt_add_one hx0
  have hRlarge : (100000 : ℝ) ≤ R := by
    simpa only [R] using hpowLarge
  have hone : (1 : ℝ) ≤ (1 / 100000 : ℝ) * R := by
    calc
      (1 : ℝ) = (1 / 100000 : ℝ) * 100000 := by norm_num
      _ ≤ (1 / 100000 : ℝ) * R :=
        mul_le_mul_of_nonneg_left hRlarge (by norm_num)
  have hdouble :
      (1 / 100000 : ℝ) * R + 1 ≤ (1 / 50000 : ℝ) * R := by
    nlinarith
  constructor
  · simpa only [R] using hscaledLower.trans hceilLower
  · dsimp only [R]
    nlinarith

/-- In particular, the shared reference time tends to infinity. -/
theorem tendsto_ndA5ReferenceLevel_atTop :
    Tendsto ndA5ReferenceLevel atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro N
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (3 / 5 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop
      (by norm_num : (0 : ℝ) < 3 / 5)).comp hlog
  filter_upwards
    [eventually_ndA5ReferenceLevel_cast_sandwich,
      hpow.eventually_ge_atTop (200000 * (N : ℝ))]
      with B hsandwich hlarge
  have hcast : (N : ℝ) ≤ (ndA5ReferenceLevel B : ℝ) := by
    calc
      (N : ℝ) = (1 / 200000 : ℝ) * (200000 * (N : ℝ)) := by
        ring
      _ ≤ (1 / 200000 : ℝ) *
          Real.rpow (Real.log B) (3 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hlarge (by norm_num)
      _ ≤ (ndA5ReferenceLevel B : ℝ) := hsandwich.1
  exact_mod_cast hcast

/-- The checked FM1 interface may therefore eventually be used at exponent
eleven, whose threshold is `150`. -/
theorem eventually_one_hundred_fifty_le_ndA5ReferenceLevel :
    ∀ᶠ B : ℕ in atTop, 150 ≤ ndA5ReferenceLevel B :=
  tendsto_ndA5ReferenceLevel_atTop.eventually_ge_atTop 150

end
end ND
end Erdos1135
