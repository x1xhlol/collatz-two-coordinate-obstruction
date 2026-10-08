/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitCanonicalCase1Threshold
import Erdos1135Predecessor.Tao.Section6.FirstCrossingPartition
import Erdos1135Predecessor.Tao.Section6.HeadSubmass

namespace Erdos1135Predecessor.ND.PositiveDensity

open Tao

open scoped BigOperators

noncomputable section

theorem explicitSection6_log_gt_four {n : ℕ} (hn : 2 ^ 80 ≤ n) :
    4 < Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ 80) hnR
  rw [Real.log_pow] at h
  have h2 := taoCor63_log_two_gt_693_div_1000
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem explicitSection6_log_budget {n : ℕ} (hn : 2 ^ 80 ≤ n)
    {D e : ℝ} (hD : 0 ≤ D) (he : 0 ≤ e) (hscale : D ≤ e * 2 ^ 40) :
    D * Real.log (n : ℝ) ≤ e * n := by
  have hnR : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have hsqr : ((2 : ℝ) ^ 40) ^ 2 ≤ n := by
    simpa only [← pow_mul, show 40 * 2 = 80 by norm_num] using hnR
  have hs := Real.sqrt_le_sqrt hsqr
  rw [Real.sqrt_sq (by positivity)] at hs
  have hDroot := hscale.trans (mul_le_mul_of_nonneg_left hs he)
  calc
    D * Real.log (n : ℝ) ≤ D * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left (explicitRenewal_log_le_sqrt hn0) hD
    _ ≤ (e * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right hDroot (Real.sqrt_nonneg _)
    _ = e * n := by rw [mul_assoc, Real.mul_self_sqrt hn0.le]

theorem explicitSection6_quarter_ratio :
    taoCor63YoungQuarterConst 16 / (-taoCor63YoungQuarterCoeff 80) < 4 := by
  have hquad := taoCor63_young_quarter_quadratic_coeff_lt
  have hlog2 := taoCor63_log_two_lt_347_div_500
  have hcoeff : taoCor63YoungQuarterCoeff 80 < -672 := by
    unfold taoCor63YoungQuarterCoeff
    nlinarith
  have hgamma : taoCor63DecayGamma ≤ (1 / 3 : ℝ) := by
    rw [taoCor63DecayGamma_eq_log_four_thirds]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    linarith
  have hconst : taoCor63YoungQuarterConst 16 < 17 := by
    unfold taoCor63YoungQuarterConst
    linarith [taoCor63_log_two_pos]
  apply (div_lt_iff₀ (show 0 < -taoCor63YoungQuarterCoeff 80 by linarith)).mpr
  linarith

theorem explicitSection6_head_small {n k l : ℕ} {head : List ℕ+}
    (hn : 2 ^ 80 ≤ n) (hgate : taoSection6HeadGate 80 n k l head) :
    taoCor63ClearedOffsetSum l head < 3 ^ n := by
  have hlog := explicitSection6_log_gt_four hn
  exact taoCor63ClearedOffsetSum_lt_of_young_quarter_lrange_log_bound_CA17_D16
    (by norm_num) (taoSection6HeadGate_weight hgate)
    (taoSection6HeadGate_typical hgate) (by linarith)
    (taoSection6HeadGate_starLRange_of_log_ge_four (by norm_num) hlog.le hgate)
    (explicitSection6_quarter_ratio.trans hlog)

theorem explicitSection6_head_inj {n k l : ℕ} (hn : 2 ^ 80 ≤ n) :
    Set.InjOn (taoCor63SourceOffsetZMod n l)
      {head | taoSection6HeadGate 80 n k l head} := by
  intro as has bs hbs heq
  exact taoCor63Star_eq_of_sourceOffsetZMod_eq_small
    ((taoSection6HeadGate_length has).trans (taoSection6HeadGate_length hbs).symm)
    (taoSection6HeadGate_weight has) (taoSection6HeadGate_weight hbs) heq
    (explicitSection6_head_small hn has) (explicitSection6_head_small hn hbs)

theorem explicitSection6_head_L2 {n : ℕ} (hn : 2 ^ 80 ≤ n) (k l : ℕ) :
    (∑ y : ZMod (3 ^ n), (taoSection6HeadSubmass 80 n k l y) ^ 2) ≤
      (1 / 2 : ℝ) ^ l := by
  unfold taoSection6HeadSubmass
  apply taoGatedSubmass_sum_sq_le
    (geom2PNatListPMF (k + 1)) (taoSection6HeadGate 80 n k l)
    (taoCor63SourceOffsetZMod n l)
  · positivity
  · exact explicitSection6_head_inj hn
  · intro head hgate
    exact (geom2PNatListPMF_apply_toReal_eq_headGate_weight hgate).le

theorem explicitSection6_head_index {n k l : ℕ} {head : List ℕ+}
    (hn : 2 ^ 80 ≤ n) (hgate : taoSection6HeadGate 80 n k l head) :
    20 * k ≤ 17 * n := by
  apply taoSection6HeadGate_index_le_of_log_budget
    (lt_trans (by norm_num) (explicitSection6_log_gt_four hn)) _ hgate
  norm_num only [Nat.cast_ofNat, OfNat.ofNat, pow_two]
  exact explicitSection6_log_budget hn (by norm_num) (by norm_num) (by norm_num)

theorem explicitSection6_global_head {n : ℕ} {full : List ℕ+}
    (hn : 2 ^ 80 ≤ n) (hglobal : taoSection6GlobalTypical 80 n full) :
    ∃ k l : ℕ, k < n ∧ l < 2 * n ∧
      taoSection6HeadGate 80 n k l (full.take (k + 1)) := by
  have hn2 : 2 ≤ n := (by norm_num : 2 ≤ (2 : ℕ) ^ 80).trans hn
  have hbudget : ((5 / 2 : ℝ) * 80 ^ 2 + 80) * Real.log (n : ℝ) ≤
      (3 / 10 : ℝ) * n :=
    explicitSection6_log_budget hn (by norm_num) (by norm_num) (by norm_num)
  have hQ := taoSection6GlobalTypical_starQ_crossing_of_log_budget
    (by norm_num) hn2 hbudget hglobal
  obtain ⟨k, hk, _⟩ := existsUnique_taoSection6PrefixCrossing hQ.1 hQ.2
  have hgate := taoSection6HeadGate_of_global_prefixCrossing hglobal hk
  refine ⟨k, taoTupleWeight (full.take (k + 1)), ?_, ?_, hgate⟩
  · simpa [taoSection6GlobalTypical_length hglobal] using hk.1
  · exact taoSection6HeadGate_weight_lt_two_mul (by norm_num) (by omega)
      (explicitSection6_log_gt_four hn).le hgate

end

end Erdos1135Predecessor.ND.PositiveDensity
