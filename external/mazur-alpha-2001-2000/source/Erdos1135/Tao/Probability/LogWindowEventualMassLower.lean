/-
Modified 2026-09-28 for the independent alpha = 2001/2000 replay of
Mazur's Proposition 1.11 formalization, pinned at ca3dd0d63920.
The changes are documented in alpha-2001-2000.patch and the replay report.
Original copyright and license notices are retained; see LICENSE and NOTICE.
-/

import Erdos1135.Tao.Probability.LogWindowQuarterMass
import Erdos1135.Tao.Probability.LogWindowEndpoints

/-!
# Eventual Mass Lower Bounds For Real And Floor Tao Windows

This neutral proof leaf supplies the four normalizer lower bounds needed to
transport the natural Proposition 1.11 rate to genuine real source windows.
It uses the rounded-window mass theorem directly, without subtracting the
floor-window symmetric-difference error.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

noncomputable section

/-- A power-base Tao window has at least `log b / 8000` mass once its
rounded width and logarithmic scale are large enough. -/
theorem log_div_eightThousand_le_taoNyOddWindow_rpow_mass
    {b beta : ℝ} (hb : 2 ≤ b) (hbeta : 1 ≤ beta)
    (hlog : 24000 ≤ Real.log b)
    (hwidth : b ^ beta + 2 ≤ (b ^ beta) ^ taoAlpha) :
    Real.log b / 8000 ≤
      logFinsetMass (taoNyOddWindow (b ^ beta) taoAlpha) := by
  have hbpos : 0 < b := by linarith
  have hbone : 1 ≤ b := by linarith
  have hbetaNonneg : 0 ≤ beta := by linarith
  have hyTwo : 2 ≤ b ^ beta := by
    exact hb.trans (Real.self_le_rpow_of_one_le hbone hbeta)
  have hyNonneg : 0 ≤ b ^ beta := (Real.rpow_pos_of_pos hbpos beta).le
  have hab : Nat.ceil (b ^ beta) ≤
      Nat.floor ((b ^ beta) ^ taoAlpha) := by
    have hsucc := taoNyLo_succ_le_taoNyHi_of_width hyNonneg hwidth
    simpa only [taoNyLo, taoNyHi] using
      (show taoNyLo (b ^ beta) ≤ taoNyHi (b ^ beta) taoAlpha by omega)
  have hlogY : Real.log (b ^ beta) = beta * Real.log b :=
    Real.log_rpow hbpos beta
  have hlogBNonneg : 0 ≤ Real.log b := by linarith
  have hlogScale : Real.log b ≤ beta * Real.log b := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hbeta hlogBNonneg
  have hlogWidth : 12 ≤ (taoAlpha - 1) * Real.log (b ^ beta) := by
    rw [hlogY]
    norm_num [taoAlpha]
    nlinarith
  have hmass := one_quarter_log_width_le_rounded_power_oddWindow_mass
    hyTwo taoAlpha_one_lt hab hlogWidth
  calc
    Real.log b / 8000 ≤ Real.log (b ^ beta) / 8000 := by
      rw [hlogY]
      exact div_le_div_of_nonneg_right hlogScale (by norm_num)
    _ = ((taoAlpha - 1) / 4) * Real.log (b ^ beta) := by
      norm_num [taoAlpha]
      ring
    _ ≤ logFinsetMass (taoNyOddWindow (b ^ beta) taoAlpha) := by
      simpa only [taoNyOddWindow, taoNyLo, taoNyHi] using hmass

/-- Every fixed power scale `beta >= 1` eventually has the standard Tao
window mass lower bound. -/
theorem eventually_log_div_eightThousand_le_taoNyOddWindow_rpow_mass
    {beta : ℝ} (hbeta : 1 ≤ beta) :
    ∀ᶠ b : ℝ in atTop,
      Real.log b / 8000 ≤
        logFinsetMass (taoNyOddWindow (b ^ beta) taoAlpha) := by
  have hbetaPos : 0 < beta := zero_lt_one.trans_le hbeta
  have hpow : Tendsto (fun b : ℝ => b ^ beta) atTop atTop :=
    tendsto_rpow_atTop hbetaPos
  have hlog : Tendsto (fun b : ℝ => Real.log b) atTop atTop :=
    Real.tendsto_log_atTop
  filter_upwards
    [eventually_ge_atTop (2 : ℝ),
      hlog.eventually_ge_atTop (24000 : ℝ),
      hpow.eventually taoNy_width_eventually]
      with b hb hlogLarge hwidth
  exact log_div_eightThousand_le_taoNyOddWindow_rpow_mass
    hb hbeta hlogLarge hwidth

/-- For `B = floor x`, both the floor-based and genuine real power windows
eventually have mass at least `log B / 8000`. -/
theorem eventually_floor_real_rpow_window_mass_lower
    {beta : ℝ} (hbeta : 1 ≤ beta) :
    ∀ᶠ x : ℝ in atTop,
      Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
          logFinsetMass
            (taoNyOddWindow
              (((Nat.floor x : ℕ) : ℝ) ^ beta) taoAlpha) ∧
        Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
          logFinsetMass (taoNyOddWindow (x ^ beta) taoAlpha) := by
  have hfloorCast :
      Tendsto (fun x : ℝ => ((Nat.floor x : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have hfloorMass := hfloorCast.eventually
    (eventually_log_div_eightThousand_le_taoNyOddWindow_rpow_mass hbeta)
  have hrealMass :=
    eventually_log_div_eightThousand_le_taoNyOddWindow_rpow_mass hbeta
  filter_upwards [hfloorMass, hrealMass, eventually_ge_atTop (2 : ℝ)]
      with x hfloorMass hrealMass hx
  refine ⟨hfloorMass, ?_⟩
  have hxpos : 0 < x := by linarith
  have hx0 : 0 ≤ x := hxpos.le
  have hfloorOne : 1 ≤ Nat.floor x :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by norm_num; linarith)
  have hfloorPos : 0 < ((Nat.floor x : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Nat.floor x by omega)
  have hlogLe : Real.log ((Nat.floor x : ℕ) : ℝ) ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn hfloorPos hxpos (Nat.floor_le hx0)
  exact (div_le_div_of_nonneg_right hlogLe (by norm_num)).trans hrealMass

/-- Eventual normalizer packet for the two Proposition 1.11 source scales. -/
structure TaoProp111RealFloorWindowMassFacts (x : ℝ) : Prop where
  one_le_x : 1 ≤ x
  log_floor_large : 8000 ≤ Real.log ((Nat.floor x : ℕ) : ℝ)
  alpha_floor :
    Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
      logFinsetMass
        (taoNyOddWindow
          (((Nat.floor x : ℕ) : ℝ) ^ taoAlpha) taoAlpha)
  alpha_real :
    Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
      logFinsetMass (taoNyOddWindow (x ^ taoAlpha) taoAlpha)
  alphaSq_floor :
    Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
      logFinsetMass
        (taoNyOddWindow
          (((Nat.floor x : ℕ) : ℝ) ^ (taoAlpha ^ 2)) taoAlpha)
  alphaSq_real :
    Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
      logFinsetMass (taoNyOddWindow (x ^ (taoAlpha ^ 2)) taoAlpha)

theorem TaoProp111RealFloorWindowMassFacts.log_floor_pos
    {x : ℝ} (facts : TaoProp111RealFloorWindowMassFacts x) :
    0 < Real.log ((Nat.floor x : ℕ) : ℝ) := by
  linarith [facts.log_floor_large]

/-- The four real/floor Proposition 1.11 source normalizers eventually satisfy
one common `log(floor x) / 8000` lower bound. -/
theorem eventually_taoProp111RealFloorWindowMassFacts :
    ∀ᶠ x : ℝ in atTop, TaoProp111RealFloorWindowMassFacts x := by
  have hfloorCast :
      Tendsto (fun x : ℝ => ((Nat.floor x : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have hlogFloor :
      Tendsto (fun x : ℝ => Real.log ((Nat.floor x : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hfloorCast
  filter_upwards
    [eventually_ge_atTop (1 : ℝ),
      hlogFloor.eventually_ge_atTop (8000 : ℝ),
      eventually_floor_real_rpow_window_mass_lower
        (show (1 : ℝ) ≤ taoAlpha by norm_num [taoAlpha]),
      eventually_floor_real_rpow_window_mass_lower
        (show (1 : ℝ) ≤ taoAlpha ^ 2 by norm_num [taoAlpha])]
      with x hx hlog hAlpha hAlphaSq
  exact ⟨hx, hlog, hAlpha.1, hAlpha.2, hAlphaSq.1, hAlphaSq.2⟩

end

end Tao
end Erdos1135
