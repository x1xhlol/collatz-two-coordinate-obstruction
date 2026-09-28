import Erdos1135.Tao.Section5.AffineSourceScale

/-!
# Section 5 Uniform Affine Denominator Ratio

This scalar leaf bounds the relative affine offset `F / M` uniformly over all
scheduled tuples and endpoints.  It contains no PMF or atom-mass statement.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Branch-independent relative-error scale for replacing `M - F` by `M`. -/
noncomputable def taoSection5AffineDenominatorRatio (B : ℕ) : ℝ :=
  (3 : ℝ) ^ taoSection5N0 B / taoSection5CanonicalLostLower B

/-- The checked reverse-prefix budget places the canonical lower endpoint
strictly above zero. -/
theorem taoSection5CanonicalLostLower_pos
    {B : ℕ} (facts : TaoSection5AffineSourceScaleFacts B) :
    0 < taoSection5CanonicalLostLower B := by
  have hmainNonneg :
      0 ≤ Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) :=
    mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg B)
  have hpowPos : 0 < (3 : ℝ) ^ taoSection5N0 B := by positivity
  exact lt_of_le_of_lt (add_nonneg hmainNonneg hpowPos.le)
    facts.reverseBudget

/-- The canonical denominator-ratio scale is nonnegative. -/
theorem taoSection5AffineDenominatorRatio_nonneg
    {B : ℕ} (facts : TaoSection5AffineSourceScaleFacts B) :
    0 ≤ taoSection5AffineDenominatorRatio B := by
  have hlowerPos := taoSection5CanonicalLostLower_pos facts
  exact div_nonneg (by positivity) hlowerPos.le

/-- Every scheduled tuple/endpoint pair has relative affine offset bounded by
the branch-independent denominator ratio. -/
theorem taoSection5_affineOffset_div_endpoint_nonneg_le
    {B n M : ℕ} {branch : TaoSection5SourceBranch} {E : Set ℕ}
    {as : List ℕ+}
    (facts : TaoSection5AffineSourceScaleFacts B)
    (hn : n ∈ taoSection5PassTimes B branch)
    (has : as ∈ taoSection5TypicalTuples B (n - taoSection5M0 B))
    (hM : M ∈ taoSection5EPrime B E) :
    0 ≤ (taoOffsetList as : ℝ) / (M : ℝ) ∧
      (taoOffsetList as : ℝ) / (M : ℝ) ≤
        taoSection5AffineDenominatorRatio B := by
  have htyp := mem_taoSection5TypicalTuples_iff.mp has
  have hMdata := mem_taoSection5EPrime_iff.mp hM
  have hMposNat : 0 < M := Odd.pos hMdata.2.2.1
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hMposNat
  have hlowerM : taoSection5CanonicalLostLower B ≤ (M : ℝ) :=
    Nat.ceil_le.mp hMdata.1
  have hlowerPos := taoSection5CanonicalLostLower_pos facts
  have hoffsetNonneg : 0 ≤ (taoOffsetList as : ℝ) :=
    Rat.cast_nonneg.mpr (taoOffsetList_nonneg as)
  have hoffsetQ := taoOffsetList_le_three_pow_length as
  have hoffsetR :
      (taoOffsetList as : ℝ) ≤ (3 : ℝ) ^ as.length := by
    exact_mod_cast hoffsetQ
  rw [htyp.1] at hoffsetR
  have hqle : n - taoSection5M0 B ≤ taoSection5N0 B :=
    facts.schedule.sub_le_n0 hn
  have hpowLe :
      (3 : ℝ) ^ (n - taoSection5M0 B) ≤
        (3 : ℝ) ^ taoSection5N0 B :=
    pow_le_pow_right₀ (by norm_num) hqle
  have hoffsetLe :
      (taoOffsetList as : ℝ) ≤ (3 : ℝ) ^ taoSection5N0 B :=
    hoffsetR.trans hpowLe
  refine ⟨div_nonneg hoffsetNonneg hMpos.le, ?_⟩
  unfold taoSection5AffineDenominatorRatio
  calc
    (taoOffsetList as : ℝ) / (M : ℝ) ≤
        (3 : ℝ) ^ taoSection5N0 B / (M : ℝ) :=
      div_le_div_of_nonneg_right hoffsetLe hMpos.le
    _ ≤ (3 : ℝ) ^ taoSection5N0 B /
        taoSection5CanonicalLostLower B :=
      div_le_div_of_nonneg_left (by positivity) hlowerPos hlowerM

/-- The exact ratio scale already has the stronger power decay
`B^(-4/5)` under the checked source-scale packet. -/
theorem taoSection5AffineDenominatorRatio_le_rpow_neg_four_fifths
    {B : ℕ} (facts : TaoSection5AffineSourceScaleFacts B) :
    taoSection5AffineDenominatorRatio B ≤
      (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have hBpos : 0 < (B : ℝ) := by
    exact_mod_cast facts.schedule.one_le_B
  have hexpOne :
      1 ≤ Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) := by
    apply Real.one_le_exp
    have hslack : 0 ≤ taoSection5TypicalSlack B := by
      unfold taoSection5TypicalSlack
      exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast
        facts.schedule.one_le_B)) _
    positivity
  have hBmain :
      (B : ℝ) ≤
        Real.exp (2 * Real.log 2 * taoSection5TypicalSlack B) * (B : ℝ) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hexpOne hBpos.le
  have hBlower : (B : ℝ) < taoSection5CanonicalLostLower B :=
    hBmain.trans_lt
      ((le_add_of_nonneg_right (by positivity :
          0 ≤ (3 : ℝ) ^ taoSection5N0 B)).trans_lt facts.reverseBudget)
  have hlowerPos : 0 < taoSection5CanonicalLostLower B :=
    hBpos.trans hBlower
  have hpowLe :
      (3 : ℝ) ^ taoSection5N0 B ≤ (B : ℝ) ^ (1 / 5 : ℝ) :=
    taoSection5_three_pow_n0_le_threshold_rpow_one_fifth
      facts.schedule.one_le_B
  unfold taoSection5AffineDenominatorRatio
  calc
    (3 : ℝ) ^ taoSection5N0 B / taoSection5CanonicalLostLower B ≤
        (B : ℝ) ^ (1 / 5 : ℝ) /
          taoSection5CanonicalLostLower B :=
      div_le_div_of_nonneg_right hpowLe hlowerPos.le
    _ ≤ (B : ℝ) ^ (1 / 5 : ℝ) / (B : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hBpos.le _)
        hBpos hBlower.le
    _ = (B : ℝ) ^ (-(4 / 5 : ℝ)) := by
      calc
        (B : ℝ) ^ (1 / 5 : ℝ) / (B : ℝ) =
            (B : ℝ) ^ (1 / 5 : ℝ) / (B : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = (B : ℝ) ^ ((1 / 5 : ℝ) - 1) :=
          (Real.rpow_sub hBpos (1 / 5 : ℝ) 1).symm
        _ = (B : ℝ) ^ (-(4 / 5 : ℝ)) := by norm_num

end

end Tao
end Erdos1135
