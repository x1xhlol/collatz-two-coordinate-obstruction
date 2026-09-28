import Erdos1135.Tao.Renewal.Prop78Boundary
import Erdos1135.Tao.Renewal.Prop78Case3FixedParameters
import Erdos1135.Tao.Renewal.QEndpointFreshOutsideEprimeWidth

/-!
# Proposition 7.8 Case 3 Eventual Scale

This source-free leaf chooses one eventual boundary-scale threshold after the
fixed Case 3 parameters and the countable `EStar` depth cutoff `S0` are known.
It deliberately contains no ambient source sample, boundary point, triangle,
or probability estimate.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

/-- The five scalar facts needed from a sufficiently large Case 3 boundary
scale. -/
structure TaoSection7Case3EventualScaleFacts
    {constants : TaoSection7Lemma710Constants}
    {A : ℕ} {epsilon : ℝ}
    (fixed : TaoSection7Case3FixedParameters constants A epsilon)
    (S0 m : ℕ) : Prop where
  two_le_m : 2 ≤ m
  P_le_m : fixed.P ≤ m
  Pmax_range :
    (fixed.Pmax : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10)
  bound_le_m_at_Pmax :
    taoSection7Case3LargeTriangleBoundWithBase
        (8 : ℝ) (4 * fixed.Aweight) fixed.Pmax ≤
      Real.rpow (m : ℝ) ((2 : ℝ) / 5)
  S0_le_boundaryThreshold :
    (S0 : ℝ) ≤ taoSection7Prop78BoundaryThreshold m

/-- The eventual scale facts directly supply the finite inclusive cap record
consumed by the countable canonical `EStar` estimate. -/
def TaoSection7Case3EventualScaleFacts.to_allowedCapAdmissibility
    {constants : TaoSection7Lemma710Constants}
    {A S0 m : ℕ} {epsilon : ℝ}
    {fixed : TaoSection7Case3FixedParameters constants A epsilon}
    (h : TaoSection7Case3EventualScaleFacts fixed S0 m) :
    TaoSection7Case3BaseKcutAllowedCapAdmissibility
      (Finset.range (fixed.Pmax + 1))
      8 m (4 * fixed.Aweight) fixed.Pmax where
  base_ge_four := by norm_num
  allowed_le_Pmax := by
    intro p hp
    have hp_lt : p < fixed.Pmax + 1 := Finset.mem_range.1 hp
    omega
  Pmax_range := h.Pmax_range
  bound_le_m_at_Pmax := h.bound_le_m_at_Pmax

/-- Every fixed Case 3 packet and depth cutoff admit one source-independent
threshold beyond which all five scale facts hold. -/
theorem exists_taoSection7Case3EventualScaleThreshold
    {constants : TaoSection7Lemma710Constants}
    {A : ℕ} {epsilon : ℝ}
    (fixed : TaoSection7Case3FixedParameters constants A epsilon)
    (S0 : ℕ) :
    ∃ Cscale : ℕ, ∀ m ≥ Cscale,
      TaoSection7Case3EventualScaleFacts fixed S0 m := by
  have hPmax : ∀ᶠ m : ℕ in Filter.atTop,
      (fixed.Pmax : ℝ) ≤
        Real.rpow (m : ℝ) ((1 : ℝ) / 10) :=
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (fixed.Pmax : ℝ))
  have hbound : ∀ᶠ m : ℕ in Filter.atTop,
      taoSection7Case3LargeTriangleBoundWithBase
          (8 : ℝ) (4 * fixed.Aweight) fixed.Pmax ≤
        Real.rpow (m : ℝ) ((2 : ℝ) / 5) :=
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (taoSection7Case3LargeTriangleBoundWithBase
          (8 : ℝ) (4 * fixed.Aweight) fixed.Pmax))
  have hS0Power : ∀ᶠ m : ℕ in Filter.atTop,
      100 * (S0 : ℝ) ≤
        Real.rpow (m : ℝ) ((4 : ℝ) / 5) :=
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (100 * (S0 : ℝ)))
  have hfacts : ∀ᶠ m : ℕ in Filter.atTop,
      TaoSection7Case3EventualScaleFacts fixed S0 m := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ),
      Filter.eventually_ge_atTop fixed.P, hPmax, hbound, hS0Power] with
      m hm hPm hPmaxm hboundm hS0m
    have hmOneNat : 1 < m := by omega
    have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hmOneNat
    have hmPos : (0 : ℝ) < (m : ℝ) := lt_trans (by norm_num) hmOne
    have hlogSqPos : 0 < (Real.log (m : ℝ)) ^ 2 :=
      pow_pos (Real.log_pos hmOne) 2
    have hlogBound :
        (Real.log (m : ℝ)) ^ 2 ≤
          100 * Real.rpow (m : ℝ) ((1 : ℝ) / 5) :=
      lemma79_log_sq_le_hundred_mul_rpow_one_fifth hmOne.le
    have hpowSum :
        Real.rpow (m : ℝ) ((4 : ℝ) / 5) *
            Real.rpow (m : ℝ) ((1 : ℝ) / 5) =
          (m : ℝ) := by
      calc
        Real.rpow (m : ℝ) ((4 : ℝ) / 5) *
              Real.rpow (m : ℝ) ((1 : ℝ) / 5) =
            Real.rpow (m : ℝ)
              (((4 : ℝ) / 5) + ((1 : ℝ) / 5)) :=
          (Real.rpow_add hmPos ((4 : ℝ) / 5) ((1 : ℝ) / 5)).symm
        _ = Real.rpow (m : ℝ) (1 : ℝ) := by norm_num
        _ = (m : ℝ) := by simp
    have hcross :
        (S0 : ℝ) * (Real.log (m : ℝ)) ^ 2 ≤ (m : ℝ) := by
      calc
        (S0 : ℝ) * (Real.log (m : ℝ)) ^ 2 ≤
            (S0 : ℝ) *
              (100 * Real.rpow (m : ℝ) ((1 : ℝ) / 5)) :=
          mul_le_mul_of_nonneg_left hlogBound (Nat.cast_nonneg S0)
        _ = (100 * (S0 : ℝ)) *
            Real.rpow (m : ℝ) ((1 : ℝ) / 5) := by ring
        _ ≤ Real.rpow (m : ℝ) ((4 : ℝ) / 5) *
            Real.rpow (m : ℝ) ((1 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_right hS0m
            (Real.rpow_nonneg hmPos.le _)
        _ = (m : ℝ) := hpowSum
    exact
      { two_le_m := hm
        P_le_m := hPm
        Pmax_range := hPmaxm
        bound_le_m_at_Pmax := hboundm
        S0_le_boundaryThreshold := by
          unfold taoSection7Prop78BoundaryThreshold
          exact (le_div_iff₀ hlogSqPos).2 hcross }
  exact Filter.eventually_atTop.mp hfacts

end

end Tao
end Erdos1135
