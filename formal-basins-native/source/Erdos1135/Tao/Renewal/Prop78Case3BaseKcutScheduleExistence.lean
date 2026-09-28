import Erdos1135.Tao.Renewal.Prop78Case3BaseKcutFiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Case 3 Factorized Slack Schedule Existence

This leaf constructs the scalar schedule used after canonical Lemma 7.10.
The recurrence exponent is fixed exactly at `Kcut = 4 * Aweight`; a larger
base absorbs the polynomial row, while quadratic exponential decay absorbs
the exponential row for all sufficiently large `Aweight`.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Quadratic decay absorbs the exact `4^(4*Aweight)` recurrence cost and
one half of the final scalar budget. -/
theorem exists_Aweight_threshold_sharpExpTail_four_mul_le_half_sq
    (constants : TaoSection7Lemma710Constants) :
    ∃ A0 : ℕ, ∀ Aweight : ℕ, A0 ≤ Aweight →
      constants.C710 *
          taoSection7Case3BaseKcutSharpExpTail constants Aweight *
          ((4 : ℝ) ^ (4 * Aweight)) ≤
        (1 / 2 : ℝ) * (Aweight : ℝ) ^ 2 := by
  have hqLim :
      Filter.Tendsto
        (fun A : ℕ =>
          256 * Real.exp (-(constants.c710 * (A : ℝ))))
        Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, Real.rpow_zero, one_mul,
      mul_comm, mul_left_comm, mul_assoc, mul_neg, neg_mul, zero_mul] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
          0 constants.c710 constants.c710_pos).comp
        tendsto_natCast_atTop_atTop).const_mul 256
  have hgeomLim :
      Filter.Tendsto
        (fun A : ℕ =>
          2 * constants.C710 * (1 / 2 : ℝ) ^ A)
        Filter.atTop (nhds 0) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc, zero_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
          (2 * constants.C710)
  rcases Filter.eventually_atTop.1
      (hqLim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)) with
    ⟨Aq, hAq⟩
  rcases Filter.eventually_atTop.1
      (hgeomLim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)) with
    ⟨Ag, hAg⟩
  let Alin : ℕ :=
    ⌈8 * Real.log 4 / constants.c710⌉₊
  let A0 : ℕ := max 1 (max Aq (max Ag Alin))
  refine ⟨A0, ?_⟩
  intro Aweight hAweight
  have hAone : 1 ≤ Aweight :=
    le_trans (Nat.le_max_left 1 _) hAweight
  have hAqWeight : Aq ≤ Aweight :=
    le_trans (le_trans (Nat.le_max_left Aq _) (Nat.le_max_right 1 _))
      hAweight
  have hAgWeight : Ag ≤ Aweight :=
    le_trans
      (le_trans
        (le_trans (Nat.le_max_left Ag Alin) (Nat.le_max_right Aq _))
        (Nat.le_max_right 1 _))
      hAweight
  have hAlinWeight : Alin ≤ Aweight :=
    le_trans
      (le_trans
        (le_trans (Nat.le_max_right Ag Alin) (Nat.le_max_right Aq _))
        (Nat.le_max_right 1 _))
      hAweight
  have hq :
      256 * Real.exp (-(constants.c710 * (Aweight : ℝ))) ≤ 1 / 2 :=
    hAq Aweight hAqWeight
  have hgeom :
      2 * constants.C710 * (1 / 2 : ℝ) ^ Aweight ≤ 1 / 2 :=
    hAg Aweight hAgWeight
  have hAreal : (1 : ℝ) ≤ Aweight := by exact_mod_cast hAone
  have hA0 : (0 : ℝ) ≤ Aweight := le_trans zero_le_one hAreal
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlinCeil :
      8 * Real.log 4 / constants.c710 ≤ (Alin : ℝ) := by
    dsimp [Alin]
    exact Nat.le_ceil _
  have hlinA :
      8 * Real.log 4 / constants.c710 ≤ (Aweight : ℝ) := by
    exact hlinCeil.trans (by exact_mod_cast hAlinWeight)
  have hlinCross :
      8 * Real.log 4 ≤ (Aweight : ℝ) * constants.c710 :=
    (div_le_iff₀ constants.c710_pos).1 hlinA
  have hlinMul := mul_le_mul_of_nonneg_left hlinCross hA0
  have hexponent :
      -(constants.c710 * (Aweight : ℝ) ^ 2) +
          4 * (Aweight : ℝ) * Real.log 4 ≤
        -(constants.c710 / 2) * (Aweight : ℝ) ^ 2 := by
    nlinarith
  have hAsq : (Aweight : ℝ) ≤ (Aweight : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hAreal)]
  have hexpSqLe :
      Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) ≤
        Real.exp (-(constants.c710 * (Aweight : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hAsq constants.c710_pos.le]
  have hexpHalf :
      Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) ≤ 1 / 2 := by
    have hsmall :
        Real.exp (-(constants.c710 * (Aweight : ℝ))) ≤ 1 / 2 := by
      nlinarith [Real.exp_pos (-(constants.c710 * (Aweight : ℝ)))]
    exact hexpSqLe.trans hsmall
  have hdenPos :
      0 < 1 - Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) := by
    nlinarith [Real.exp_pos (-(constants.c710 * (Aweight : ℝ) ^ 2))]
  have hinv :
      (1 - Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)))⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hdenPos]
    nlinarith
  have hpow4 :
      ((4 : ℝ) ^ (4 * Aweight)) = (256 : ℝ) ^ Aweight := by
    rw [pow_mul]
    norm_num
  have hexpPow :
      Real.exp (-(constants.c710 * (Aweight : ℝ))) ^ Aweight =
        Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfactor :
      Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) *
          ((4 : ℝ) ^ (4 * Aweight)) =
        (256 * Real.exp (-(constants.c710 * (Aweight : ℝ)))) ^ Aweight := by
    rw [hpow4, mul_pow, hexpPow]
    ring
  have hq0 :
      0 ≤ 256 * Real.exp (-(constants.c710 * (Aweight : ℝ))) := by
    positivity
  have hqPow :
      (256 * Real.exp (-(constants.c710 * (Aweight : ℝ)))) ^ Aweight ≤
        (1 / 2 : ℝ) ^ Aweight :=
    pow_le_pow_left₀ hq0 hq Aweight
  unfold taoSection7Case3BaseKcutSharpExpTail
  calc
    constants.C710 *
          (Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) *
            (1 - Real.exp
              (-(constants.c710 * (Aweight : ℝ) ^ 2)))⁻¹) *
          (4 : ℝ) ^ (4 * Aweight) =
        constants.C710 *
          (1 - Real.exp
            (-(constants.c710 * (Aweight : ℝ) ^ 2)))⁻¹ *
          (Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) *
            (4 : ℝ) ^ (4 * Aweight)) := by ring
    _ ≤ constants.C710 * 2 *
          (Real.exp (-(constants.c710 * (Aweight : ℝ) ^ 2)) *
            (4 : ℝ) ^ (4 * Aweight)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv constants.C710_nonneg)
        (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by norm_num) _))
    _ = constants.C710 * 2 *
          (256 * Real.exp
            (-(constants.c710 * (Aweight : ℝ)))) ^ Aweight := by
      rw [hfactor]
    _ ≤ constants.C710 * 2 * (1 / 2 : ℝ) ^ Aweight := by
      exact mul_le_mul_of_nonneg_left hqPow
        (mul_nonneg constants.C710_nonneg (by norm_num))
    _ = 2 * constants.C710 * (1 / 2 : ℝ) ^ Aweight := by ring
    _ ≤ 1 / 2 := hgeom
    _ ≤ (1 / 2 : ℝ) * (Aweight : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((Aweight : ℝ) - 1)]

/-- For every sufficiently large `Aweight`, one can choose a polynomial base
while keeping the recurrence exponent exactly `4 * Aweight`. -/
theorem exists_baseKcutFactorizedSlackSchedule_four_mul
    (constants : TaoSection7Lemma710Constants) :
    ∃ A0 : ℕ, ∀ Aweight : ℕ, A0 ≤ Aweight →
      ∃ base : ℕ,
        Nonempty
          (TaoSection7Case3BaseKcutFactorizedSlackSchedule
            Aweight base (4 * Aweight) constants) := by
  rcases exists_Aweight_threshold_sharpExpTail_four_mul_le_half_sq constants with
    ⟨A0, hExp⟩
  refine ⟨max 1 A0, ?_⟩
  intro Aweight hAweight
  have hAone : 1 ≤ Aweight :=
    le_trans (Nat.le_max_left 1 A0) hAweight
  have hA0 : A0 ≤ Aweight :=
    le_trans (Nat.le_max_right 1 A0) hAweight
  let N : ℕ := max 1 ⌈4 * constants.C710⌉₊
  let base : ℕ := 4 * N
  have hNone : 1 ≤ N := Nat.le_max_left 1 _
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hNone
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hNone
  have hNCeil :
      4 * constants.C710 ≤ (N : ℝ) := by
    calc
      4 * constants.C710 ≤ (⌈4 * constants.C710⌉₊ : ℕ) :=
        Nat.le_ceil _
      _ ≤ (N : ℝ) := by
        exact_mod_cast (Nat.le_max_right 1 ⌈4 * constants.C710⌉₊)
  have hKpos : 0 < 4 * Aweight := by omega
  have hNpow : (N : ℝ) ≤ (N : ℝ) ^ (4 * Aweight) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hKpos)
    rw [hk, pow_succ]
    have honePow : (1 : ℝ) ≤ (N : ℝ) ^ k := one_le_pow₀ hNreal
    nlinarith [show (0 : ℝ) ≤ N by positivity]
  have hfourCpow :
      4 * constants.C710 ≤ (N : ℝ) ^ (4 * Aweight) :=
    hNCeil.trans hNpow
  have hNpowPos : 0 < (N : ℝ) ^ (4 * Aweight) := by positivity
  have hpolyHalf :
      constants.C710 * 2 / (N : ℝ) ^ (4 * Aweight) ≤ 1 / 2 := by
    apply (div_le_iff₀ hNpowPos).2
    nlinarith
  refine ⟨base, ⟨{
      base_ge_four := by
        dsimp [base]
        omega
      polySlack := 1 / 2
      expSlack := 1 / 2
      polySlack_nonneg := by norm_num
      expSlack_nonneg := by norm_num
      slack_sum := by norm_num
      polynomial_base_slack := ?_
      exponential_kcut_slack := ?_ }⟩⟩
  · calc
      constants.C710 * 2 *
          ((4 : ℝ) ^ (4 * Aweight) /
            (base : ℝ) ^ (4 * Aweight)) =
        constants.C710 * 2 / (N : ℝ) ^ (4 * Aweight) := by
          dsimp [base]
          push_cast
          rw [mul_pow]
          field_simp
      _ ≤ 1 / 2 := hpolyHalf
  · simpa using hExp Aweight hA0

/-- Route-facing selector with the fixed base `8`: for every requested lower
bound, choose one sufficiently large `Aweight` and retain the exact recurrence
exponent `4 * Aweight`. -/
theorem exists_baseKcutFactorizedSlackSchedule_eight_four_mul
    (constants : TaoSection7Lemma710Constants) (Amin : ℕ) :
    ∃ Aweight : ℕ,
      max Amin 8 ≤ Aweight ∧
        Nonempty
          (TaoSection7Case3BaseKcutFactorizedSlackSchedule
            Aweight 8 (4 * Aweight) constants) := by
  rcases exists_Aweight_threshold_sharpExpTail_four_mul_le_half_sq constants with
    ⟨Aexp, hExp⟩
  have hpolyLim :
      Filter.Tendsto
        (fun A : ℕ =>
          2 * constants.C710 * (1 / 16 : ℝ) ^ A)
        Filter.atTop (nhds 0) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc, zero_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 16)
        (by norm_num : (1 / 16 : ℝ) < 1)).const_mul
          (2 * constants.C710)
  rcases Filter.eventually_atTop.1
      (hpolyLim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)) with
    ⟨Apoly, hpoly⟩
  let Aweight : ℕ := max (max Amin 8) (max Aexp Apoly)
  have hrequested : max Amin 8 ≤ Aweight := Nat.le_max_left _ _
  have hAexp : Aexp ≤ Aweight :=
    le_trans (Nat.le_max_left Aexp Apoly) (Nat.le_max_right _ _)
  have hApoly : Apoly ≤ Aweight :=
    le_trans (Nat.le_max_right Aexp Apoly) (Nat.le_max_right _ _)
  have hpolyHalf :
      2 * constants.C710 * (1 / 16 : ℝ) ^ Aweight ≤ 1 / 2 :=
    hpoly Aweight hApoly
  refine ⟨Aweight, hrequested, ⟨{
      base_ge_four := by norm_num
      polySlack := 1 / 2
      expSlack := 1 / 2
      polySlack_nonneg := by norm_num
      expSlack_nonneg := by norm_num
      slack_sum := by norm_num
      polynomial_base_slack := ?_
      exponential_kcut_slack := by
        simpa using hExp Aweight hAexp }⟩⟩
  calc
    constants.C710 * 2 *
        ((4 : ℝ) ^ (4 * Aweight) / (8 : ℝ) ^ (4 * Aweight)) =
      2 * constants.C710 * (1 / 16 : ℝ) ^ Aweight := by
        rw [pow_mul, pow_mul, ← div_pow]
        norm_num
        ring
    _ ≤ 1 / 2 := hpolyHalf

/-- The base-`8`, exact-four-times selector supplies the scalar absorption
record on every later inclusive offset range.  No source scale or boundary
sample is chosen here. -/
theorem exists_baseKcutFiniteSumAbsorptionInputs_eight_four_mul
    (constants : TaoSection7Lemma710Constants) (Amin : ℕ) :
    ∃ Aweight : ℕ,
      max Amin 8 ≤ Aweight ∧
        ∀ Pmax : ℕ,
          Nonempty
            (TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs
              (Finset.range (Pmax + 1))
              Aweight 8 (4 * Aweight) constants) := by
  rcases
      exists_baseKcutFactorizedSlackSchedule_eight_four_mul constants Amin with
    ⟨Aweight, hAweight, hschedule⟩
  refine ⟨Aweight, hAweight, ?_⟩
  intro Pmax
  rcases hschedule with ⟨schedule⟩
  have hApos : 0 < Aweight := by omega
  have hrows :
      TaoSection7Case3BaseKcutScalarRowInputs
        (Finset.range (Pmax + 1)) Aweight 8 (4 * Aweight) constants :=
    TaoSection7Case3BaseKcutScalarRowInputs.of_factorizedSlackSchedule
      (allowed := Finset.range (Pmax + 1))
      (Aweight := Aweight) (base := 8) (Kcut := 4 * Aweight)
      (m := Pmax + 1) (constants := constants)
      schedule hApos (by
        intro p hp
        exact Finset.mem_range.1 hp)
  exact
    ⟨TaoSection7Case3BaseKcutFiniteSumAbsorptionInputs.of_scalarRows hrows⟩

end

end Tao
end Erdos1135
