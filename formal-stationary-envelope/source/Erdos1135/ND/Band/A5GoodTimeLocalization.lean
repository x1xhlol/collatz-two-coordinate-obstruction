import Erdos1135.ND.Band.A5BandSourceWindow
import Erdos1135.ND.Band.A5PrefixGood
import Erdos1135.Tao.Section5.DeterministicDescent
import Erdos1135.Tao.Section5.PassTimeLocalization
import Erdos1135.Tao.Syracuse.FirstPassageInterval

/-!
# A5 Good-Time Localization

This leaf turns the frozen strict full-prefix Good event into the deterministic
first-passage window used by J3.  The passage remains conditional on the
checked Section 5 descent and time-room packets; no probability estimate is
used here.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Strict FullGood at the scheduled horizon forces enough valuation weight
for inherited deterministic descent. -/
private theorem ndA5FullPrefixGoodEvent_weight_at_n0
    {B : ℕ} {C : ℝ} {N : Tao.TaoOddNat}
    (hWn0 :
      10 * ndA5TubeWidth B C ≤ (Tao.taoSection5N0 B : ℝ))
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C) :
    19 * Tao.taoSection5N0 B ≤
      10 * Tao.taoTupleWeight
        (Tao.syracuseValuationPNatList
          (Tao.taoSection5N0 B) N.1 N.2) := by
  have hdeviation := hgood.2 (Tao.taoSection5N0 B) le_rfl
  rw [Tao.syracuseValuationPNatList_take_of_le N.2 le_rfl] at hdeviation
  have hlower := (abs_lt.mp hdeviation).1
  have hreal :
      (19 : ℝ) * Tao.taoSection5N0 B <
        10 * Tao.taoTupleWeight
          (Tao.syracuseValuationPNatList
            (Tao.taoSection5N0 B) N.1 N.2) := by
    nlinarith
  exact_mod_cast hreal.le

/-- A first hit issued from a valid band and a strict FullGood prefix occurs
no later than the common horizon `n0`. -/
theorem ndA5_firstHit_le_n0_of_fullPrefixGood
    {B n j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {N : Tao.TaoOddNat}
    (descent : Tao.TaoSection5DescentScaleFacts B)
    (hWn0 :
      10 * ndA5TubeWidth B C ≤ (Tao.taoSection5N0 B : ℝ))
    (hj : j < ndA5BandCount B branch)
    (hband : N.1 ∈ ndA5OddBand B branch j)
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C)
    (hfirst : Tao.syracuseFirstHitAtMost B N.1 n) :
    n ≤ Tao.taoSection5N0 B := by
  have hsource := ndA5OddBand_mem_taoSection5SourceWindow
    descent.one_le_B hj hband
  have hweight := ndA5FullPrefixGoodEvent_weight_at_n0 hWn0 hgood
  have hterminal := descent.iterate_le_threshold hsource hweight
  by_contra hn
  exact (not_lt_of_ge hterminal) (hfirst.2 _ (by omega))

/-- Terminal first passage plus the strict upper Good deviation gives the
lower real-time edge needed for the padded carrier. -/
private theorem ndA5_firstHit_log_lower
    {B n : ℕ} {C : ℝ} {N : Tao.TaoOddNat}
    (hB : 1 ≤ B) (hn : 0 < n)
    (hn0 : n ≤ Tao.taoSection5N0 B)
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C)
    (hfirst : Tao.syracuseFirstHitAtMost B N.1 n) :
    Real.log ((N.1 : ℝ) / (B : ℝ)) / ndA5LogFourThirds -
        ndA5TubeWidth B C / ndA5PhaseDelta < (n : ℝ) := by
  let as := Tao.syracuseValuationPNatList n N.1 N.2
  let S := Tao.taoTupleWeight as
  have hgoodn := ndA5FullPrefixGoodEvent_prefix hgood hn0
  have htake : as.take n = as := by
    rw [← hgoodn.1]
    exact List.take_length
  have hdeviation := hgoodn.2 n le_rfl
  rw [htake] at hdeviation
  have hone : 1 ≤ n := hn
  have hfirst' :
      Tao.syracuseFirstHitAtMost B N.1 (n - 1 + 1) := by
    simpa [Nat.sub_add_cancel hone] using hfirst
  have hclearedNat : 3 ^ n * N.1 ≤ B * 2 ^ S := by
    simpa [as, S, Nat.sub_add_cancel hone] using
      (Tao.syracuseFirstHitAtMost_terminal_upper_cleared
        (r := n - 1) N.2 hfirst')
  have hcleared :
      (3 : ℝ) ^ n * (N.1 : ℝ) ≤ (B : ℝ) * (2 : ℝ) ^ S := by
    exact_mod_cast hclearedNat
  have hNpos : (0 : ℝ) < N.1 := by
    exact_mod_cast Odd.pos N.2
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log
    (mul_pos (pow_pos (by norm_num) n) hNpos) hcleared
  rw [Real.log_mul (pow_ne_zero _ (by norm_num)) hNpos.ne',
    Real.log_mul hBpos.ne' (pow_ne_zero _ (by norm_num)),
    Real.log_pow, Real.log_pow] at hlog
  have hlogFourThirds :
      ndA5LogFourThirds = 2 * Real.log 2 - Real.log 3 := by
    unfold ndA5LogFourThirds
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have hraw :
      Real.log ((N.1 : ℝ) / (B : ℝ)) <
        (n : ℝ) * ndA5LogFourThirds +
          ndA5TubeWidth B C * Real.log 2 := by
    rw [Real.log_div hNpos.ne' hBpos.ne']
    dsimp [S] at hlog hdeviation
    rw [hlogFourThirds]
    nlinarith [(abs_lt.mp hdeviation).2]
  apply (sub_lt_iff_lt_add).2
  apply (div_lt_iff₀ ndA5LogFourThirds_pos).2
  calc
    Real.log ((N.1 : ℝ) / (B : ℝ)) <
        (n : ℝ) * ndA5LogFourThirds +
          ndA5TubeWidth B C * Real.log 2 := hraw
    _ = ((n : ℝ) + ndA5TubeWidth B C / ndA5PhaseDelta) *
          ndA5LogFourThirds := by
      rw [ndA5LogFourThirds_eq_phaseDelta_mul_logTwo]
      field_simp [ndA5PhaseDelta_mem_Ioo.1.ne']

/-- Preterminal first passage plus the strict lower Good deviation gives the
upper real-time edge.  The final `+1` is the predecessor-to-hit shift. -/
private theorem ndA5_firstHit_log_upper
    {B n : ℕ} {C : ℝ} {N : Tao.TaoOddNat}
    (hB : 1 ≤ B) (hn : 0 < n)
    (hn0 : n ≤ Tao.taoSection5N0 B)
    (time : Tao.TaoSection5PassTimeLocalizationFacts B)
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C)
    (hfirst : Tao.syracuseFirstHitAtMost B N.1 n) :
    (n : ℝ) <
      Real.log ((N.1 : ℝ) / (B : ℝ)) / ndA5LogFourThirds +
        (ndA5TubeWidth B C + 1) / ndA5PhaseDelta + 1 := by
  let r := n - 1
  let as := Tao.syracuseValuationPNatList r N.1 N.2
  let S := Tao.taoTupleWeight as
  have hone : 1 ≤ n := hn
  have hrn : r + 1 = n := by dsimp [r]; omega
  have hrn0 : r ≤ Tao.taoSection5N0 B := by dsimp [r]; omega
  have hgoodr := ndA5FullPrefixGoodEvent_prefix hgood hrn0
  have htake : as.take r = as := by
    rw [← hgoodr.1]
    exact List.take_length
  have hdeviation := hgoodr.2 r le_rfl
  rw [htake] at hdeviation
  have hpow :
      (3 : ℝ) ^ r ≤ (3 : ℝ) ^ Tao.taoSection5N0 B :=
    pow_le_pow_right₀ (by norm_num) hrn0
  have hroomReal : (2 : ℝ) * (3 : ℝ) ^ r ≤ (B : ℝ) :=
    (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans time.offset_room
  have hroom : 2 * 3 ^ r ≤ B := by exact_mod_cast hroomReal
  have hfirst' : Tao.syracuseFirstHitAtMost B N.1 (r + 1) := by
    simpa [hrn] using hfirst
  have hclearedNat : B * 2 ^ S < 2 * 3 ^ r * N.1 := by
    simpa [as, S] using
      (Tao.syracuseFirstHitAtMost_prefix_lower_cleared
        (r := r) N.2 hroom hfirst')
  have hcleared :
      (B : ℝ) * (2 : ℝ) ^ S <
        (2 : ℝ) * (3 : ℝ) ^ r * (N.1 : ℝ) := by
    exact_mod_cast hclearedNat
  have hNpos : (0 : ℝ) < N.1 := by
    exact_mod_cast Odd.pos N.2
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog := Real.log_lt_log
    (mul_pos hBpos (pow_pos (by norm_num) S)) hcleared
  rw [Real.log_mul hBpos.ne' (pow_ne_zero _ (by norm_num)),
    Real.log_pow,
    Real.log_mul
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) hNpos.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (pow_ne_zero _ (by norm_num)),
    Real.log_pow] at hlog
  have hlogFourThirds :
      ndA5LogFourThirds = 2 * Real.log 2 - Real.log 3 := by
    unfold ndA5LogFourThirds
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have hraw :
      (r : ℝ) * ndA5LogFourThirds <
        Real.log ((N.1 : ℝ) / (B : ℝ)) +
          (ndA5TubeWidth B C + 1) * Real.log 2 := by
    rw [Real.log_div hNpos.ne' hBpos.ne']
    dsimp [S] at hlog hdeviation
    rw [hlogFourThirds]
    nlinarith [(abs_lt.mp hdeviation).1]
  have hscaled :
      (r : ℝ) <
        Real.log ((N.1 : ℝ) / (B : ℝ)) / ndA5LogFourThirds +
          (ndA5TubeWidth B C + 1) / ndA5PhaseDelta := by
    calc
      (r : ℝ) <
          (Real.log ((N.1 : ℝ) / (B : ℝ)) +
              (ndA5TubeWidth B C + 1) * Real.log 2) /
            ndA5LogFourThirds :=
        (lt_div_iff₀ ndA5LogFourThirds_pos).2 hraw
      _ = Real.log ((N.1 : ℝ) / (B : ℝ)) / ndA5LogFourThirds +
            (ndA5TubeWidth B C + 1) / ndA5PhaseDelta := by
        rw [add_div, ndA5LogFourThirds_eq_phaseDelta_mul_logTwo]
        field_simp [ndA5PhaseDelta_mem_Ioo.1.ne']
  calc
    (n : ℝ) = (r : ℝ) + 1 := by
      dsimp [r]
      rw [Nat.cast_sub hone]
      norm_num
    _ < (Real.log ((N.1 : ℝ) / (B : ℝ)) / ndA5LogFourThirds +
          (ndA5TubeWidth B C + 1) / ndA5PhaseDelta) + 1 :=
      by simpa [add_comm, add_left_comm, add_assoc] using
        add_lt_add_right hscaled (1 : ℝ)
    _ = _ := by ring

/-- The inherited descent packet forces the natural threshold above one. -/
private theorem two_le_of_taoSection5DescentScaleFacts
    {B : ℕ} (descent : Tao.TaoSection5DescentScaleFacts B) :
    2 ≤ B := by
  by_contra hB
  have hn0 := descent.five_le_n0
  have hsmall : B = 0 ∨ B = 1 := by omega
  rcases hsmall with rfl | rfl <;>
    norm_num [Tao.taoSection5N0] at hn0

/-- A valid A5 source band starts strictly above its threshold. -/
private theorem threshold_lt_of_mem_ndA5OddBand
    {B N j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hB : 2 ≤ B) (hj : j < ndA5BandCount B branch)
    (hband : N ∈ ndA5OddBand B branch j) :
    B < N := by
  have hsource := ndA5OddBand_mem_taoSection5SourceWindow
    (by omega : 1 ≤ B) hj hband
  have hlower := (Tao.oddLogWindow_mem.mp hsource).1
  change Nat.ceil (Tao.taoSection5SourceY B branch) ≤ N at hlower
  have hYN : Tao.taoSection5SourceY B branch ≤ (N : ℝ) :=
    Nat.ceil_le.mp hlower
  have hBgt : (1 : ℝ) < B := by exact_mod_cast hB
  have hexponent :
      (1 : ℝ) < Tao.taoSection5BranchExponent branch := by
    cases branch <;>
      norm_num [Tao.taoSection5BranchExponent, Tao.taoAlpha]
  have hBY : (B : ℝ) < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    calc
      (B : ℝ) = (B : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (B : ℝ) ^ Tao.taoSection5BranchExponent branch :=
        Real.strictMono_rpow_of_base_gt_one hBgt hexponent
  exact_mod_cast hBY.trans_le hYN

/-- Strict FullGood localizes every first hit from a valid band in the exact
padded natural window consumed by J3. -/
theorem ndA5_firstHit_mem_paddedBandWindow_of_fullPrefixGood
    {B n j : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {N : Tao.TaoOddNat}
    (descent : Tao.TaoSection5DescentScaleFacts B)
    (time : Tao.TaoSection5PassTimeLocalizationFacts B)
    (hWn0 :
      10 * ndA5TubeWidth B C ≤ (Tao.taoSection5N0 B : ℝ))
    (hWlarge : 6 ≤ ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch)
    (hband : N.1 ∈ ndA5OddBand B branch j)
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C)
    (hfirst : Tao.syracuseFirstHitAtMost B N.1 n) :
    n ∈ ndA5PaddedBandWindow B branch C j := by
  have hn0 := ndA5_firstHit_le_n0_of_fullPrefixGood
    descent hWn0 hj hband hgood hfirst
  have hBN : B < N.1 := threshold_lt_of_mem_ndA5OddBand
    (two_le_of_taoSection5DescentScaleFacts descent) hj hband
  have hn : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact (not_lt_of_ge hfirst.1) hBN
  have hlowerTime := ndA5_firstHit_log_lower
    descent.one_le_B hn hn0 hgood hfirst
  have hupperTime := ndA5_firstHit_log_upper
    descent.one_le_B hn hn0 time hgood hfirst
  have hbandBounds := mem_ndA5OddBand_exp_iff.mp hband
  have hBpos : (0 : ℝ) < B := by exact_mod_cast descent.one_le_B
  have hNpos : (0 : ℝ) < N.1 := by exact_mod_cast Odd.pos N.2
  have hzpos : 0 < ndA5BandLower B branch j := by
    have hYpos : 0 < Tao.taoSection5SourceY B branch := by
      rw [Tao.taoSection5SourceY_eq_branch_rpow]
      exact Real.rpow_pos_of_pos hBpos _
    unfold ndA5BandLower
    positivity
  have huppos :
      0 < ndA5BandLower B branch j *
        Real.exp (ndA5BandBeta B branch) := by positivity
  have hlogLower :
      Real.log (ndA5BandLower B branch j / (B : ℝ)) ≤
        Real.log ((N.1 : ℝ) / (B : ℝ)) := by
    apply Real.log_le_log (div_pos hzpos hBpos)
    exact div_le_div_of_nonneg_right hbandBounds.1 hBpos.le
  have hlogUpper :
      Real.log ((N.1 : ℝ) / (B : ℝ)) <
        Real.log
          (ndA5BandLower B branch j *
            Real.exp (ndA5BandBeta B branch) / (B : ℝ)) := by
    apply Real.log_lt_log (div_pos hNpos hBpos)
    exact div_lt_div_of_pos_right hbandBounds.2.1 hBpos
  have hlogLowerScaled :=
    div_le_div_of_nonneg_right hlogLower ndA5LogFourThirds_pos.le
  have hlogUpperScaled :=
    (div_lt_div_iff_of_pos_right ndA5LogFourThirds_pos).2 hlogUpper
  have hmargin := ndA5FirstPassagePaddingMargin hWlarge
  have hpaddedLower : ndA5PaddedBandLower B branch C j < (n : ℝ) := by
    unfold ndA5PaddedBandLower
    calc
      Real.log (ndA5BandLower B branch j / (B : ℝ)) /
            ndA5LogFourThirds - 3 * ndA5TubeWidth B C ≤
          Real.log ((N.1 : ℝ) / (B : ℝ)) /
              ndA5LogFourThirds -
            ndA5TubeWidth B C / ndA5PhaseDelta := by
        linarith
      _ < (n : ℝ) := hlowerTime
  have hpaddedUpper : (n : ℝ) < ndA5PaddedBandUpper B branch C j := by
    unfold ndA5PaddedBandUpper
    calc
      (n : ℝ) <
          Real.log ((N.1 : ℝ) / (B : ℝ)) / ndA5LogFourThirds +
            (ndA5TubeWidth B C + 1) / ndA5PhaseDelta + 1 := hupperTime
      _ ≤ Real.log
            (ndA5BandLower B branch j *
              Real.exp (ndA5BandBeta B branch) / (B : ℝ)) /
              ndA5LogFourThirds + 3 * ndA5TubeWidth B C := by
        linarith
  apply mem_ndA5PaddedBandWindow_iff.mpr
  constructor
  · exact Nat.ceil_le.mpr hpaddedLower.le
  · have huppNonneg : 0 ≤ ndA5PaddedBandUpper B branch C j :=
      (Nat.cast_nonneg n).trans hpaddedUpper.le
    exact (Nat.le_floor_iff huppNonneg).mpr hpaddedUpper.le

end

end ND
end Erdos1135
