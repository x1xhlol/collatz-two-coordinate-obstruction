import Erdos1135.ND.Band.A5Physical
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A5 Physical Padding Rate

This A5-owned leaf proves that every fixed positive physical tube constant
eventually satisfies the shared logarithmic padding guard.  It contains no A6
or carrier-specific input.
-/

namespace Erdos1135
namespace ND

noncomputable section

private theorem tendsto_taoSection5N0_atTop_for_padding :
    Filter.Tendsto Tao.taoSection5N0 Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro n
  filter_upwards [Filter.eventually_ge_atTop (2 ^ (10 * n) : ℕ)] with B hB
  have hlog : 10 * n ≤ Nat.log 2 B :=
    Nat.le_log_of_pow_le (by norm_num) hB
  unfold Tao.taoSection5N0
  omega

/-- Every fixed positive physical tube constant eventually satisfies the
source padding inequality shared by A5 and the physical A6 interior route. -/
theorem eventually_three_mul_ndA5TubeWidth_le_log
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ B : ℕ in Filter.atTop,
      3 * ndA5TubeWidth B C ≤
        (33 / 500000 : ℝ) * Real.log B := by
  let k : ℝ := 33 / 500000
  let d : ℝ := 10 * Real.log 2
  let epsilon : ℝ := k * d / (3 * C)
  have hk : 0 < k := by norm_num [k]
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hrealPow : Filter.Tendsto
      (fun x : ℝ => Real.log x ^ (1 / 2 : ℝ) / x ^ (1 / 2 : ℝ))
      Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hreal : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.log x) / Real.sqrt x)
      Filter.atTop (nhds 0) := by
    apply hrealPow.congr'
    filter_upwards [] with x
    simp [Real.sqrt_eq_rpow]
  have hschedule : Filter.Tendsto
      (fun B : ℕ => (Tao.taoSection5N0 B : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp
      tendsto_taoSection5N0_atTop_for_padding
  have hsmall : ∀ᶠ B : ℕ in Filter.atTop,
      Real.sqrt (Real.log (Tao.taoSection5N0 B : ℝ)) /
          Real.sqrt (Tao.taoSection5N0 B : ℝ) < epsilon :=
    (hreal.comp hschedule).eventually_lt_const hepsilon
  have hlarge : ∀ᶠ B : ℕ in Filter.atTop,
      (2 : ℝ) ≤ (Tao.taoSection5N0 B : ℝ) :=
    hschedule.eventually_ge_atTop 2
  filter_upwards [hsmall, hlarge] with B hsmallB hNtwo
  let N : ℝ := Tao.taoSection5N0 B
  let L := Real.log N
  let r := Real.sqrt L / Real.sqrt N
  have hNtwo' : (2 : ℝ) ≤ N := by simpa [N] using hNtwo
  have hNpos : 0 < N := by linarith
  have hsqrtNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hrSmall : r < epsilon := by
    simpa [r, L, N] using hsmallB
  have hNroot : Real.sqrt N * Real.sqrt N = N := by
    nlinarith [Real.sq_sqrt hNpos.le]
  have hroot : Real.sqrt (N * L) = N * r := by
    rw [Real.sqrt_mul hNpos.le]
    dsimp [r]
    calc
      Real.sqrt N * Real.sqrt L =
          (Real.sqrt N * Real.sqrt N) *
            (Real.sqrt L / Real.sqrt N) := by
        field_simp [hsqrtNpos.ne']
      _ = N * (Real.sqrt L / Real.sqrt N) := by rw [hNroot]
  have hNdiv : N ≤ Real.log B / d := by
    simpa [N, d] using Tao.taoSection5N0_le_log_div_ten_log_two B
  have hNd : N * d ≤ Real.log B := (le_div_iff₀ hd).mp hNdiv
  change 3 * (C * Real.sqrt (N * L)) ≤ k * Real.log B
  rw [hroot]
  calc
    3 * (C * (N * r)) = (3 * C * N) * r := by ring
    _ ≤ (3 * C * N) * epsilon :=
      mul_le_mul_of_nonneg_left hrSmall.le (by positivity)
    _ = k * (N * d) := by
      dsimp [epsilon]
      field_simp [hC.ne']
      <;> ring
    _ ≤ k * Real.log B := mul_le_mul_of_nonneg_left hNd hk.le

/-- Every fixed positive physical tube is eventually narrower than Tao's
inherited `log(B)^(3/5)` source-typicality slack. -/
theorem eventually_ndA5TubeWidth_le_taoSection5TypicalSlack
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ B : ℕ in Filter.atTop,
      ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B := by
  let epsilon : ℝ := 1 / C
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hrealPow : Filter.Tendsto
      (fun x : ℝ =>
        Real.log x ^ (1 / 2 : ℝ) / x ^ (1 / 10 : ℝ))
      Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 10)).tendsto_div_nhds_zero
  have hreal : Filter.Tendsto
      (fun x : ℝ =>
        Real.sqrt (Real.log x) / Real.rpow x (1 / 10 : ℝ))
      Filter.atTop (nhds 0) := by
    apply hrealPow.congr'
    filter_upwards [] with x
    simp [Real.sqrt_eq_rpow]
  have hschedule : Filter.Tendsto
      (fun B : ℕ => (Tao.taoSection5N0 B : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp
      tendsto_taoSection5N0_atTop_for_padding
  have hsmall : ∀ᶠ B : ℕ in Filter.atTop,
      Real.sqrt (Real.log (Tao.taoSection5N0 B : ℝ)) /
          Real.rpow (Tao.taoSection5N0 B : ℝ) (1 / 10 : ℝ) <
        epsilon :=
    (hreal.comp hschedule).eventually_lt_const hepsilon
  have hlarge : ∀ᶠ B : ℕ in Filter.atTop,
      (2 : ℝ) ≤ (Tao.taoSection5N0 B : ℝ) :=
    hschedule.eventually_ge_atTop 2
  filter_upwards [hsmall, hlarge] with B hsmallB hNtwo
  let N : ℝ := Tao.taoSection5N0 B
  let L : ℝ := Real.log N
  have hNpos : 0 < N := by
    have : (0 : ℝ) < 2 := by norm_num
    exact this.trans_le (by simpa [N] using hNtwo)
  have hpowPos : 0 < Real.rpow N (1 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hNpos _
  have hrSmall :
      Real.sqrt L / Real.rpow N (1 / 10 : ℝ) < epsilon := by
    simpa [N, L] using hsmallB
  have hLSmall :
      Real.sqrt L ≤ epsilon * Real.rpow N (1 / 10 : ℝ) :=
    ((div_lt_iff₀ hpowPos).mp hrSmall).le
  have hlogTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hdPos : 0 < 10 * Real.log 2 := by positivity
  have hdOne : (1 : ℝ) ≤ 10 * Real.log 2 := by
    nlinarith
  have hNdiv :
      N ≤ Real.log B / (10 * Real.log 2) := by
    simpa [N] using Tao.taoSection5N0_le_log_div_ten_log_two B
  have hNd : N * (10 * Real.log 2) ≤ Real.log B :=
    (le_div_iff₀ hdPos).mp hNdiv
  have hNleLog : N ≤ Real.log B := by
    calc
      N = N * 1 := by ring
      _ ≤ N * (10 * Real.log 2) :=
        mul_le_mul_of_nonneg_left hdOne hNpos.le
      _ ≤ Real.log B := hNd
  have hCepsilon : C * epsilon = 1 := by
    dsimp [epsilon]
    field_simp [hC.ne']
  have hNfactor :
      Real.sqrt N * Real.rpow N (1 / 10 : ℝ) =
        Real.rpow N (3 / 5 : ℝ) := by
    calc
      Real.sqrt N * Real.rpow N (1 / 10 : ℝ) =
          Real.rpow N (1 / 2 : ℝ) * Real.rpow N (1 / 10 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        change Real.rpow N (1 / 2 : ℝ) *
          Real.rpow N (1 / 10 : ℝ) = _
        rfl
      _ = Real.rpow N ((1 / 2 : ℝ) + (1 / 10 : ℝ)) :=
        (Real.rpow_add hNpos (1 / 2 : ℝ) (1 / 10 : ℝ)).symm
      _ = Real.rpow N (3 / 5 : ℝ) := by norm_num
  change C * Real.sqrt (N * L) ≤
    Real.rpow (Real.log B) (3 / 5 : ℝ)
  calc
    C * Real.sqrt (N * L) =
        (C * Real.sqrt N) * Real.sqrt L := by
      rw [Real.sqrt_mul hNpos.le]
      ring
    _ ≤ (C * Real.sqrt N) *
          (epsilon * Real.rpow N (1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hLSmall
        (mul_nonneg hC.le (Real.sqrt_nonneg N))
    _ = (C * epsilon) *
          (Real.sqrt N * Real.rpow N (1 / 10 : ℝ)) := by ring
    _ = Real.rpow N (3 / 5 : ℝ) := by
      rw [hCepsilon, one_mul, hNfactor]
    _ ≤ Real.rpow (Real.log B) (3 / 5 : ℝ) :=
      Real.rpow_le_rpow hNpos.le hNleLog (by norm_num)

end

end ND
end Erdos1135
