import Erdos1135.Tao.Fourier.Lemma74PrimitiveStrip

/-!
# Lemma 7.4 Claim-Star Scalars

This proof leaf packages the scalar inequalities used by the three cases of
Tao's Claim (*). It does not construct selectors, triangles, or families.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Elementary numerical bound used by the Claim (*) envelope. -/
theorem taoSection7_exp_neg_six_lt_one_hundredth :
    Real.exp (-6) < (1 / 100 : ℝ) := by
  have hbase : (8 / 5 : ℝ) ≤ Real.exp (3 / 5 : ℝ) := by
    have h := Real.add_one_le_exp (3 / 5 : ℝ)
    norm_num at h ⊢
    exact h
  have hpow : (8 / 5 : ℝ) ^ 10 ≤ (Real.exp (3 / 5 : ℝ)) ^ 10 := by
    gcongr
  have hexpPow : (Real.exp (3 / 5 : ℝ)) ^ 10 = Real.exp 6 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hhundred : (100 : ℝ) < (8 / 5 : ℝ) ^ 10 := by norm_num
  have hhundredExp : (100 : ℝ) < Real.exp 6 := by
    rw [← hexpPow]
    exact hhundred.trans_le hpow
  simpa [Real.exp_neg] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 100) hhundredExp)

/-- Scalar hypotheses shared by the three cases of Tao's Claim (*). -/
structure TaoSection7ClaimStarScalarPacket (epsilon : ℝ) : Prop where
  epsilon_pos : 0 < epsilon
  separation_one : 1 ≤ taoSection7TriangleSeparation epsilon
  combined_weak :
    epsilon * Real.exp
        ((Real.log 9 + Real.log 2) *
          taoSection7TriangleSeparation epsilon) ≤
      (1 / 100 : ℝ)
  inset_margin :
    1 + taoSection7TriangleSeparation epsilon ≤
      taoSection7TriangleLogScale epsilon / Real.log 9

/-- The concrete source regime `epsilon <= exp(-10)` supplies every scalar
input needed by the three cases of Claim (*). -/
theorem TaoSection7ClaimStarScalarPacket.of_le_exp_neg_ten
    {epsilon : ℝ} (hepsilon0 : 0 < epsilon)
    (hepsilon10 : epsilon ≤ Real.exp (-10)) :
    TaoSection7ClaimStarScalarPacket epsilon := by
  let L : ℝ := taoSection7TriangleLogScale epsilon
  let rho : ℝ := taoSection7TriangleSeparation epsilon
  have hlogEpsilon : Real.log epsilon ≤ (-10 : ℝ) :=
    (Real.log_le_iff_le_exp hepsilon0).2 hepsilon10
  have hL : 10 ≤ L := by
    have hneg := neg_le_neg hlogEpsilon
    simpa [L, taoSection7TriangleLogScale, one_div, Real.log_inv] using hneg
  have hrho : rho = L / 10 := by
    simp only [rho, taoSection7TriangleSeparation, L]
    ring
  have hexpNegTen100 : Real.exp (-10) ≤ (1 / 100 : ℝ) := by
    exact (Real.exp_le_exp.mpr (by norm_num : (-10 : ℝ) ≤ -6)).trans
      taoSection7_exp_neg_six_lt_one_hundredth.le
  have hepsilon100 : epsilon ≤ (1 / 100 : ℝ) :=
    hepsilon10.trans hexpNegTen100
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogThreeHalves : Real.log (3 / 2 : ℝ) ≤ 1 / 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    norm_num at h
    exact h
  have hlog3Eq :
      Real.log (3 : ℝ) = Real.log 2 + Real.log (3 / 2 : ℝ) := by
    calc
      Real.log (3 : ℝ) = Real.log (2 * (3 / 2 : ℝ)) := by norm_num
      _ = Real.log 2 + Real.log (3 / 2 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
  have hlog9Eq : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogs : Real.log 9 + Real.log 2 ≤ 4 := by
    rw [hlog9Eq, hlog3Eq]
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hweighted :
      (Real.log 9 + Real.log 2) * rho ≤ 2 * L / 5 := by
    rw [hrho]
    have hmul := mul_le_mul_of_nonneg_right hlogs
      (div_nonneg hL0 (by norm_num : (0 : ℝ) ≤ 10))
    nlinarith
  have hepsilonEq : epsilon = Real.exp (-L) := by
    have hnegL : -L = Real.log epsilon := by
      simp [L, taoSection7TriangleLogScale, one_div, Real.log_inv]
    calc
      epsilon = Real.exp (Real.log epsilon) := (Real.exp_log hepsilon0).symm
      _ = Real.exp (-L) := by rw [hnegL]
  refine
    { epsilon_pos := hepsilon0
      separation_one := ?_
      combined_weak := ?_
      inset_margin := ?_ }
  · change 1 ≤ rho
    rw [hrho]
    nlinarith
  · have harg :
        -L + (Real.log 9 + Real.log 2) * rho ≤ -6 := by
      linarith
    calc
      epsilon * Real.exp
          ((Real.log 9 + Real.log 2) * rho) =
          Real.exp (-L + (Real.log 9 + Real.log 2) * rho) := by
            rw [hepsilonEq, Real.exp_add]
      _ ≤ Real.exp (-6) := Real.exp_le_exp.mpr harg
      _ ≤ (1 / 100 : ℝ) :=
        taoSection7_exp_neg_six_lt_one_hundredth.le
  · exact one_add_taoSection7TriangleSeparation_le_logScale_div_log9
      hepsilon0 hepsilon100

theorem TaoSection7ClaimStarScalarPacket.epsilon_le_one_hundredth
    {epsilon : ℝ} (h : TaoSection7ClaimStarScalarPacket epsilon) :
    epsilon ≤ (1 / 100 : ℝ) := by
  have hrho : 0 ≤ taoSection7TriangleSeparation epsilon :=
    zero_le_one.trans h.separation_one
  have hlogs : 0 ≤ Real.log (9 : ℝ) + Real.log (2 : ℝ) :=
    add_nonneg (Real.log_pos (by norm_num)).le
      (Real.log_pos (by norm_num)).le
  have harg :
      0 ≤ (Real.log 9 + Real.log 2) *
        taoSection7TriangleSeparation epsilon :=
    mul_nonneg hlogs hrho
  have honeExp :
      (1 : ℝ) ≤ Real.exp
        ((Real.log 9 + Real.log 2) *
          taoSection7TriangleSeparation epsilon) := by
    simpa using Real.exp_le_exp.mpr harg
  calc
    epsilon = epsilon * 1 := by ring
    _ ≤ epsilon * Real.exp
        ((Real.log 9 + Real.log 2) *
          taoSection7TriangleSeparation epsilon) :=
      mul_le_mul_of_nonneg_left honeExp h.epsilon_pos.le
    _ ≤ (1 / 100 : ℝ) := h.combined_weak

theorem TaoSection7ClaimStarScalarPacket.epsilon_lt_one_hundredth
    {epsilon : ℝ} (h : TaoSection7ClaimStarScalarPacket epsilon) :
    epsilon < (1 / 100 : ℝ) := by
  have hrho : 0 < taoSection7TriangleSeparation epsilon :=
    zero_lt_one.trans_le h.separation_one
  have hlogs : 0 < Real.log (9 : ℝ) + Real.log (2 : ℝ) :=
    add_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))
  have harg :
      0 < (Real.log 9 + Real.log 2) *
        taoSection7TriangleSeparation epsilon :=
    mul_pos hlogs hrho
  have honeExp :
      (1 : ℝ) < Real.exp
        ((Real.log 9 + Real.log 2) *
          taoSection7TriangleSeparation epsilon) := by
    simpa using Real.exp_lt_exp.mpr harg
  calc
    epsilon = epsilon * 1 := by ring
    _ < epsilon * Real.exp
        ((Real.log 9 + Real.log 2) *
          taoSection7TriangleSeparation epsilon) :=
      mul_lt_mul_of_pos_left honeExp h.epsilon_pos
    _ ≤ (1 / 100 : ℝ) := h.combined_weak

theorem TaoSection7ClaimStarScalarPacket.log_two_weak
    {epsilon : ℝ} (h : TaoSection7ClaimStarScalarPacket epsilon) :
    epsilon * Real.exp
        (Real.log 2 * taoSection7TriangleSeparation epsilon) ≤
      (1 / 100 : ℝ) := by
  have hrho : 0 ≤ taoSection7TriangleSeparation epsilon :=
    zero_le_one.trans h.separation_one
  have hlog9 : 0 ≤ Real.log (9 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  calc
    epsilon * Real.exp
        (Real.log 2 * taoSection7TriangleSeparation epsilon) ≤
        epsilon * Real.exp
          ((Real.log 9 + Real.log 2) *
            taoSection7TriangleSeparation epsilon) := by
          apply mul_le_mul_of_nonneg_left _ h.epsilon_pos.le
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right (by linarith) hrho
    _ ≤ (1 / 100 : ℝ) := h.combined_weak

theorem TaoSection7ClaimStarScalarPacket.log_nine_weak
    {epsilon : ℝ} (h : TaoSection7ClaimStarScalarPacket epsilon) :
    epsilon * Real.exp
        (Real.log 9 * taoSection7TriangleSeparation epsilon) ≤
      (1 / 100 : ℝ) := by
  have hrho : 0 ≤ taoSection7TriangleSeparation epsilon :=
    zero_le_one.trans h.separation_one
  have hlog2 : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  calc
    epsilon * Real.exp
        (Real.log 9 * taoSection7TriangleSeparation epsilon) ≤
        epsilon * Real.exp
          ((Real.log 9 + Real.log 2) *
            taoSection7TriangleSeparation epsilon) := by
          apply mul_le_mul_of_nonneg_left _ h.epsilon_pos.le
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right (by linarith) hrho
    _ ≤ (1 / 100 : ℝ) := h.combined_weak

theorem TaoSection7ClaimStarScalarPacket.combined_lt_half
    {epsilon : ℝ} (h : TaoSection7ClaimStarScalarPacket epsilon) :
    epsilon * Real.exp
        ((Real.log 9 + Real.log 2) *
          taoSection7TriangleSeparation epsilon) <
      (1 / 2 : ℝ) :=
  h.combined_weak.trans_lt (by norm_num)

end

end Tao
end Erdos1135
