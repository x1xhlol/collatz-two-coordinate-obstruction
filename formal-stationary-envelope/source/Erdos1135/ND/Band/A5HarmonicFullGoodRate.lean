import Erdos1135.ND.Band.A5Physical
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A5 FullGood Rate Absorption

This scalar-only leaf absorbs the two terms of the checked harmonic FullGood
complement envelope into the frozen power-ten logarithmic budget.  The
conservative hypothesis `40 ≤ C` remains visible and no branch, probability,
event, or terminal-coverage hypothesis enters the proof.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

private theorem tendsto_taoSection5N0_atTop_for_fullGoodRate :
    Tendsto Tao.taoSection5N0 atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro n
  filter_upwards [Filter.eventually_ge_atTop (2 ^ (10 * n) : ℕ)] with B hB
  have hlog : 10 * n ≤ Nat.log 2 B :=
    Nat.le_log_of_pow_le (by norm_num) hB
  unfold Tao.taoSection5N0
  omega

private theorem eventually_four_mul_log_n0_le_sqrt :
    ∀ᶠ B : ℕ in atTop,
      4 * Real.log (Tao.taoSection5N0 B : ℝ) ≤
        Real.sqrt
          ((Tao.taoSection5N0 B : ℝ) *
            Real.log (Tao.taoSection5N0 B : ℝ)) := by
  have hsmallReal :=
    Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 16)
  have hsmallNat := hsmallReal.natCast_atTop
  have hschedule : Tendsto Tao.taoSection5N0 atTop atTop :=
    tendsto_taoSection5N0_atTop_for_fullGoodRate
  filter_upwards
      [hschedule.eventually hsmallNat, hschedule.eventually_ge_atTop 1]
    with B hsmall hn
  let N : ℝ := Tao.taoSection5N0 B
  have hNone : (1 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hN0 : 0 ≤ N := by positivity
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNone
  have hsmall' : Real.log N ≤ (1 / 16 : ℝ) * N := by
    simpa only [N, Real.norm_eq_abs, abs_of_nonneg hlog0, id_eq,
      abs_of_nonneg hN0] using hsmall
  have hlogBound : 16 * Real.log N ≤ N := by
    nlinarith [hsmall']
  have hbase : 0 ≤ N * Real.log N := mul_nonneg hN0 hlog0
  have hsq :
      (4 * Real.log N) ^ 2 ≤ (Real.sqrt (N * Real.log N)) ^ 2 := by
    rw [Real.sq_sqrt hbase]
    nlinarith [mul_le_mul_of_nonneg_right hlogBound hlog0]
  exact (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).1 hsq

private theorem twelve_mul_log_n0_le_radius_min
    {B : ℕ} {C : ℝ}
    (hC : (40 : ℝ) ≤ C)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hn : 1 ≤ Tao.taoSection5N0 B)
    (hroot :
      4 * Real.log (Tao.taoSection5N0 B : ℝ) ≤
        Real.sqrt
          ((Tao.taoSection5N0 B : ℝ) *
            Real.log (Tao.taoSection5N0 B : ℝ))) :
    12 * Real.log (Tao.taoSection5N0 B : ℝ) ≤
      min
        ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 /
          (32 * (Tao.taoSection5N0 B : ℝ)))
        ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8) := by
  let N : ℝ := Tao.taoSection5N0 B
  let W : ℝ := ndA5TubeWidth B C
  let R : ℝ := ndA5TubeRadius W
  have hNone : (1 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := zero_lt_one.trans_le hNone
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNone
  have hroot' : 4 * Real.log N ≤ Real.sqrt (N * Real.log N) := by
    simpa only [N] using hroot
  have hW142 : (142 : ℝ) ≤ W := by
    simpa only [W] using ndA5TubeWidth_ge_one_hundred_forty_two
      (by linarith : (1 / 2 : ℝ) ≤ C) hlogB
  have hRraw : W - 1 ≤ R := by
    simpa only [R] using
      ndA5TubeWidth_sub_one_le_radius (W := W) (by linarith)
  have hRW : (3 / 4 : ℝ) * W ≤ R := by
    calc
      (3 / 4 : ℝ) * W ≤ W - 1 := by linarith
      _ ≤ R := hRraw
  have hRroot : 30 * Real.sqrt (N * Real.log N) ≤ R := by
    calc
      30 * Real.sqrt (N * Real.log N) ≤
          ((3 / 4 : ℝ) * C) * Real.sqrt (N * Real.log N) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      _ = (3 / 4 : ℝ) * W := by
        simp only [W, ndA5TubeWidth, N]
        ring
      _ ≤ R := hRW
  have hR0 : 0 ≤ R := by positivity
  have hbase : 0 ≤ N * Real.log N := mul_nonneg hNpos.le hlogN
  have hRsq :
      (30 * Real.sqrt (N * Real.log N)) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (by positivity) hR0).2 hRroot
  have h384 : 384 * N * Real.log N ≤ R ^ 2 := by
    calc
      384 * N * Real.log N ≤ 900 * (N * Real.log N) := by
        nlinarith [hbase]
      _ = (30 * Real.sqrt (N * Real.log N)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hbase]
        norm_num
      _ ≤ R ^ 2 := hRsq
  have hquad :
      12 * Real.log N ≤ R ^ 2 / (32 * N) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * N)).2
    calc
      12 * Real.log N * (32 * N) = 384 * N * Real.log N := by ring
      _ ≤ R ^ 2 := h384
  have h120 : 120 * Real.log N ≤ R := by
    calc
      120 * Real.log N ≤ 30 * Real.sqrt (N * Real.log N) := by
        nlinarith
      _ ≤ R := hRroot
  have hlinear : 12 * Real.log N ≤ R / 8 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    nlinarith
  simpa only [N, R, W] using le_min hquad hlinear

private theorem eventually_sixteen_mul_log_pow_ten_le_n0_pow_eleven :
    ∀ᶠ B : ℕ in atTop,
      16 * (Real.log (B : ℝ)) ^ 10 ≤
        (Tao.taoSection5N0 B : ℝ) ^ 11 := by
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hlog.eventually_ge_atTop
        (max 20 (16 * (20 : ℝ) ^ 11))]
    with B hlarge
  let L : ℝ := Real.log (B : ℝ)
  let N : ℝ := Tao.taoSection5N0 B
  let ell : ℝ := Real.log 2
  have hL20 : (20 : ℝ) ≤ L := by
    exact (le_max_left 20 (16 * (20 : ℝ) ^ 11)).trans
      (by simpa only [L] using hlarge)
  have hLlarge : 16 * (20 : ℝ) ^ 11 ≤ L := by
    exact (le_max_right 20 (16 * (20 : ℝ) ^ 11)).trans
      (by simpa only [L] using hlarge)
  have hLpos : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have hell : 0 < ell := Real.log_pos (by norm_num)
  have hellOne : ell < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hnLower : L / (10 * ell) - 1 < N := by
    simpa only [L, N, ell] using
      Tao.log_div_ten_log_two_sub_one_lt_taoSection5N0 B
  have hratio : L / 10 ≤ L / (10 * ell) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hell)).2
    calc
      L / 10 * (10 * ell) = L * ell := by ring
      _ ≤ L * 1 := mul_le_mul_of_nonneg_left hellOne.le hL0
      _ = L := by ring
  have hLN : L / 20 ≤ N := by
    linarith
  have hpow : (L / 20) ^ 11 ≤ N ^ 11 :=
    pow_le_pow_left₀ (div_nonneg hL0 (by norm_num)) hLN 11
  have hmul :
      (16 * (20 : ℝ) ^ 11) * L ^ 10 ≤ L * L ^ 10 :=
    mul_le_mul_of_nonneg_right hLlarge (pow_nonneg hL0 10)
  have hleft : 16 * L ^ 10 ≤ (L / 20) ^ 11 := by
    rw [div_pow]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (20 : ℝ) ^ 11)).2
    calc
      16 * L ^ 10 * 20 ^ 11 =
          (16 * (20 : ℝ) ^ 11) * L ^ 10 := by ring
      _ ≤ L * L ^ 10 := hmul
      _ = L ^ 11 := by
        rw [pow_succ]
        ring
  simpa only [L, N] using hleft.trans hpow

private theorem eventually_geom_prefix_envelope_le_eighth
    (C : ℝ) (hC : (40 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in atTop,
      2 * (Tao.taoSection5N0 B : ℝ) *
          Real.exp
            (-min
              ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 /
                (32 * (Tao.taoSection5N0 B : ℝ)))
              ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8)) ≤
        (1 / 8 : ℝ) *
          Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) := by
  have hschedule : Tendsto Tao.taoSection5N0 atTop atTop :=
    tendsto_taoSection5N0_atTop_for_fullGoodRate
  have hlog : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hlog.eventually_ge_atTop (300000 : ℝ),
        hschedule.eventually_ge_atTop 1,
        eventually_four_mul_log_n0_le_sqrt,
        eventually_sixteen_mul_log_pow_ten_le_n0_pow_eleven]
    with B hlogB hn hroot hpower
  let N : ℝ := Tao.taoSection5N0 B
  let L : ℝ := Real.log (B : ℝ)
  let Q : ℝ :=
    min
      ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 / (32 * N))
      ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8)
  have hNone : (1 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := zero_lt_one.trans_le hNone
  have hLpos : 0 < L := by
    dsimp only [L]
    linarith
  have hmin : 12 * Real.log N ≤ Q := by
    simpa only [N, Q] using
      twelve_mul_log_n0_le_radius_min hC hlogB hn hroot
  have hexp :
      Real.exp (-Q) ≤ Real.exp (-(12 * Real.log N)) :=
    Real.exp_le_exp.mpr (neg_le_neg hmin)
  have hexpPow :
      Real.exp (-(12 * Real.log N)) = 1 / N ^ 12 := by
    rw [show -(12 * Real.log N) =
        -(((12 : ℕ) : ℝ) * Real.log N) by norm_num,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hNpos]
    simp [one_div]
  have hgeom : 2 * N * Real.exp (-Q) ≤ 2 / N ^ 11 := by
    calc
      2 * N * Real.exp (-Q) ≤
          2 * N * Real.exp (-(12 * Real.log N)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 2 / N ^ 11 := by
        rw [hexpPow, pow_succ]
        field_simp [hNpos.ne']
  have hpower' : 16 * L ^ 10 ≤ N ^ 11 := by
    simpa only [L, N] using hpower
  have hNpowPos : 0 < N ^ 11 := pow_pos hNpos 11
  have hLpowPos : 0 < L ^ 10 := pow_pos hLpos 10
  have hfrac : 2 / N ^ 11 ≤ 1 / (8 * L ^ 10) := by
    apply (div_le_div_iff₀ hNpowPos
      (mul_pos (by norm_num) hLpowPos)).2
    nlinarith
  have hneg :
      Real.rpow L (-10 : ℝ) = 1 / L ^ 10 := by
    have hrpowTen : Real.rpow L (10 : ℝ) = L ^ 10 := by
      simpa only using Real.rpow_natCast L 10
    calc
      Real.rpow L (-10 : ℝ) =
          (Real.rpow L (10 : ℝ))⁻¹ := by
        simpa only using Real.rpow_neg hLpos.le (10 : ℝ)
      _ = (L ^ 10)⁻¹ := by rw [hrpowTen]
      _ = 1 / L ^ 10 := (one_div (L ^ 10)).symm
  calc
    2 * (Tao.taoSection5N0 B : ℝ) *
        Real.exp
          (-min
            ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 /
              (32 * (Tao.taoSection5N0 B : ℝ)))
            ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8)) =
      2 * N * Real.exp (-Q) := by rfl
    _ ≤ 2 / N ^ 11 := hgeom
    _ ≤ 1 / (8 * L ^ 10) := hfrac
    _ = (1 / 8 : ℝ) * Real.rpow L (-10 : ℝ) := by
      rw [hneg]
      ring
    _ = (1 / 8 : ℝ) *
        Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) := by rfl

private theorem eventually_prop19_envelope_le_eighth :
    ∀ᶠ B : ℕ in atTop,
      4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ))) ≤
        (1 / 8 : ℝ) * Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) := by
  let logB : ℕ → ℝ := fun B => Real.log (B : ℝ)
  let K : ℝ := 4 * Real.exp (Real.log 2 / 128)
  have hlog : Tendsto logB atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay :
      Tendsto
        (fun L : ℝ =>
          K * L ^ (10 : ℝ) *
            Real.exp (-(1 / 1280 : ℝ) * L))
        atTop (nhds 0) := by
    simpa only [K, mul_assoc, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (10 : ℝ) (1 / 1280 : ℝ) (by norm_num)).const_mul K
  have hsmall :
      ∀ᶠ B : ℕ in atTop,
        K * (logB B) ^ (10 : ℝ) *
            Real.exp (-(1 / 1280 : ℝ) * logB B) ≤ (1 / 8 : ℝ) :=
    (hdecay.comp hlog).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [hlog.eventually_ge_atTop (1 : ℝ), hsmall]
    with B hlogOne hsmallB
  let L := Real.log (B : ℝ)
  let ell := Real.log (2 : ℝ)
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hell : 0 < ell := Real.log_pos (by norm_num)
  have hnLower :
      L / (10 * ell) - 1 < (Tao.taoSection5N0 B : ℝ) := by
    simpa only [L, ell] using
      Tao.log_div_ten_log_two_sub_one_lt_taoSection5N0 B
  have hcoefNeg : -(ell / 128) < 0 := by
    have : 0 < ell / 128 := div_pos hell (by norm_num)
    linarith
  have hmul := mul_lt_mul_of_neg_left hnLower hcoefNeg
  have hright :
      -(ell / 128) * (L / (10 * ell) - 1) =
        ell / 128 - L / 1280 := by
    field_simp [hell.ne']
    ring
  rw [hright] at hmul
  have hexponent :
      ell * (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ))) ≤
        ell / 128 - L / 1280 := by
    nlinarith
  have hrate :
      4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ))) ≤
        4 * Real.exp (ell / 128) * Real.exp (-L / 1280) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      4 * Real.exp
          (Real.log 2 *
            (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ)))) ≤
        4 * Real.exp (ell / 128 - L / 1280) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by simpa only [ell] using hexponent))
            (by norm_num)
      _ = 4 * Real.exp (ell / 128) * Real.exp (-L / 1280) := by
        rw [show ell / 128 - L / 1280 =
            ell / 128 + (-L / 1280) by ring, Real.exp_add]
        ring
  have hpowpos : 0 < Real.rpow L (10 : ℝ) :=
    Real.rpow_pos_of_pos hLpos _
  have hscaled :
      (4 * Real.exp (ell / 128) * Real.exp (-L / 1280)) *
          Real.rpow L (10 : ℝ) ≤ (1 / 8 : ℝ) := by
    calc
      (4 * Real.exp (ell / 128) * Real.exp (-L / 1280)) *
          Real.rpow L (10 : ℝ) =
        K * Real.rpow L (10 : ℝ) *
          Real.exp (-(1 / 1280 : ℝ) * L) := by
            dsimp only [K, ell]
            ring
      _ ≤ (1 / 8 : ℝ) := by
        simpa only [logB, L] using hsmallB
  have henvelope :
      4 * Real.exp (ell / 128) * Real.exp (-L / 1280) ≤
        (1 / 8 : ℝ) / Real.rpow L (10 : ℝ) :=
    (le_div_iff₀ hpowpos).2 hscaled
  have hneg :
      Real.rpow L (-10 : ℝ) =
        1 / Real.rpow L (10 : ℝ) := by
    calc
      Real.rpow L (-10 : ℝ) =
          (Real.rpow L (10 : ℝ))⁻¹ := by
            simpa only using Real.rpow_neg hLpos.le (10 : ℝ)
      _ = 1 / Real.rpow L (10 : ℝ) :=
        (one_div (Real.rpow L (10 : ℝ))).symm
  calc
    4 * (2 : ℝ) ^
        (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ))) ≤
      4 * Real.exp (ell / 128) * Real.exp (-L / 1280) := hrate
    _ ≤ (1 / 8 : ℝ) / Real.rpow L (10 : ℝ) := henvelope
    _ = (1 / 8 : ℝ) * Real.rpow L (-10 : ℝ) := by
      rw [hneg]
      ring
    _ = (1 / 8 : ℝ) *
        Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) := by rfl

/-- For every conservative source constant `C ≥ 40`, the complete checked
harmonic FullGood-complement envelope eventually fits inside one quarter of
the frozen power-ten logarithmic budget. -/
theorem eventually_ndA5HarmonicFullGoodEnvelope_le_quarter_log_rpow_neg_ten
    (C : ℝ) (hC : (40 : ℝ) ≤ C) :
    ∀ᶠ B : ℕ in atTop,
      2 * (Tao.taoSection5N0 B : ℝ) *
          Real.exp
            (-min
              ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 /
                (32 * (Tao.taoSection5N0 B : ℝ)))
              ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8)) +
        4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ))) ≤
      (1 / 4 : ℝ) *
        Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) := by
  filter_upwards
      [eventually_geom_prefix_envelope_le_eighth C hC,
        eventually_prop19_envelope_le_eighth]
    with B hgeom hprop
  calc
    2 * (Tao.taoSection5N0 B : ℝ) *
          Real.exp
            (-min
              ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 /
                (32 * (Tao.taoSection5N0 B : ℝ)))
              ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8)) +
        4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ))) ≤
      (1 / 8 : ℝ) * Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) +
        (1 / 8 : ℝ) * Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) :=
      add_le_add hgeom hprop
    _ = (1 / 4 : ℝ) *
        Real.rpow (Real.log (B : ℝ)) (-10 : ℝ) := by ring

end

end ND
end Erdos1135
