import Erdos1135.ND.Fourier.FixedTotalDisintegration
import Erdos1135.ND.Fourier.FixedTotalTail

/-!
# Fixed-Total Bridge Tail

This leaf assembles the two inclusive fixed-bars count tails into the source
order-statistic deviation bound.  The Nat-valued image is always pulled back
to the finite dependent split carrier before finite probability lemmas are
used; no `Fintype Nat` instance is introduced.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

private theorem ndPmfProb_decideEvent_eq_of_map_eq
    {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (f : α → Bool) (g : β → Bool)
    (hmap : p.map f = q.map g) (b : Bool) :
    Tao.pmfProb p {a | f a = b} =
      Tao.pmfProb q {a | g a = b} := by
  rw [Tao.pmfProb_singleton_eq_map_apply_toReal,
    Tao.pmfProb_singleton_eq_map_apply_toReal, hmap]

private theorem ndT3_ratio_bounds
    (n j L : ℕ) (hn : 3 ≤ n) (hjn : j < n)
    (hnL : n ≤ L) (hL3n : L ≤ 3 * n) :
    (1 : ℝ) / 4 ≤
        (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) ∧
      (j : ℝ) - 1 ≤
        (j : ℝ) * (L : ℝ) / (n : ℝ) *
          (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) ∧
      (j : ℝ) * (L : ℝ) / (n : ℝ) *
          (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) ≤
        (j : ℝ) := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL1 : 1 < L := by omega
  have hn1cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hL1cast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hnLR : (n : ℝ) ≤ (L : ℝ) := by exact_mod_cast hnL
  have hL3nR : (L : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hL3n
  have hjnR : (j : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hjn)
  have hquarterCross :
      ((L : ℝ) - 1) / 4 ≤ (n : ℝ) - 1 := by
    nlinarith
  have hquarter :
      (1 : ℝ) / 4 ≤
        (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) := by
    rw [hn1cast, hL1cast]
    rw [le_div_iff₀ (by nlinarith : 0 < (L : ℝ) - 1)]
    nlinarith
  have hcrossUpper :
      (L : ℝ) * ((n : ℝ) - 1) ≤
        (n : ℝ) * ((L : ℝ) - 1) := by
    nlinarith
  have hcrossLower :
      ((j : ℝ) - 1) * ((n : ℝ) * ((L : ℝ) - 1)) ≤
        (j : ℝ) * ((L : ℝ) * ((n : ℝ) - 1)) := by
    have hprod1 : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
      mul_nonneg (by positivity) (by linarith)
    have hprod2 :
        0 ≤ ((n : ℝ) - (j : ℝ)) * ((L : ℝ) - (n : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hden : 0 < (n : ℝ) * ((L : ℝ) - 1) :=
    mul_pos hnR (by nlinarith)
  have hcenterEq :
      (j : ℝ) * (L : ℝ) / (n : ℝ) *
          (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) =
        ((j : ℝ) * ((L : ℝ) * ((n : ℝ) - 1))) /
          ((n : ℝ) * ((L : ℝ) - 1)) := by
    rw [hn1cast, hL1cast]
    field_simp
  refine ⟨hquarter, ?_, ?_⟩
  · rw [hcenterEq]
    exact (le_div_iff₀ hden).2 hcrossLower
  · rw [hcenterEq]
    apply (div_le_iff₀ hden).2
    exact mul_le_mul_of_nonneg_left hcrossUpper (by positivity)

private theorem ndT3_lower_exp_le
    (j q : ℕ) (hj : 0 < j) (hq : 0 < q) (hq3j : q ≤ 3 * j)
    (u : ℝ) :
    Real.exp (-2 * (u / 4) ^ 2 / (q : ℝ)) ≤
      Real.exp (-(u ^ 2) / (63 * (j : ℝ))) := by
  apply Real.exp_le_exp.mpr
  have hjR : 0 < (j : ℝ) := by positivity
  have hqR : 0 < (q : ℝ) := by positivity
  have hq3jR : (q : ℝ) ≤ 3 * (j : ℝ) := by
    exact_mod_cast hq3j
  have hfrac :
      u ^ 2 / (63 * (j : ℝ)) ≤ u ^ 2 / (8 * (q : ℝ)) := by
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) hjR)
      (mul_pos (by norm_num) hqR)).2
    have h8q63j : 8 * (q : ℝ) ≤ 63 * (j : ℝ) := by
      nlinarith
    exact mul_le_mul_of_nonneg_left h8q63j (sq_nonneg u)
  calc
    -2 * (u / 4) ^ 2 / (q : ℝ) =
        -(u ^ 2 / (8 * (q : ℝ))) := by field_simp; ring
    _ ≤ -(u ^ 2 / (63 * (j : ℝ))) := neg_le_neg hfrac
    _ = -(u ^ 2) / (63 * (j : ℝ)) := by ring

private theorem ndT3_upper_exp_le
    (j q : ℕ) (hj : 0 < j) (hq : 0 < q) (hq6j : q ≤ 6 * j)
    (u : ℝ) (hu8 : 8 ≤ u) :
    Real.exp (-2 * ((u - 1) / 4) ^ 2 / (q : ℝ)) ≤
      Real.exp (-(u ^ 2) / (63 * (j : ℝ))) := by
  apply Real.exp_le_exp.mpr
  have hjR : 0 < (j : ℝ) := by positivity
  have hqR : 0 < (q : ℝ) := by positivity
  have hq6jR : (q : ℝ) ≤ 6 * (j : ℝ) := by
    exact_mod_cast hq6j
  have hscalar : 48 * u ^ 2 ≤ 63 * (u - 1) ^ 2 := by
    nlinarith [sq_nonneg (u - 8)]
  have h8q48j : 8 * (q : ℝ) ≤ 48 * (j : ℝ) := by
    nlinarith
  have hcross :
      u ^ 2 * (8 * (q : ℝ)) ≤
        (u - 1) ^ 2 * (63 * (j : ℝ)) := by
    have hj0 : 0 ≤ (j : ℝ) := by positivity
    calc
      u ^ 2 * (8 * (q : ℝ)) ≤ u ^ 2 * (48 * (j : ℝ)) :=
        mul_le_mul_of_nonneg_left h8q48j (sq_nonneg u)
      _ = (48 * u ^ 2) * (j : ℝ) := by ring
      _ ≤ (63 * (u - 1) ^ 2) * (j : ℝ) :=
        mul_le_mul_of_nonneg_right hscalar hj0
      _ = (u - 1) ^ 2 * (63 * (j : ℝ)) := by ring
  have hfrac :
      u ^ 2 / (63 * (j : ℝ)) ≤
        (u - 1) ^ 2 / (8 * (q : ℝ)) := by
    exact (div_le_div_iff₀
      (mul_pos (by norm_num) hjR)
      (mul_pos (by norm_num) hqR)).2 hcross
  calc
    -2 * ((u - 1) / 4) ^ 2 / (q : ℝ) =
        -((u - 1) ^ 2 / (8 * (q : ℝ))) := by field_simp; ring
    _ ≤ -(u ^ 2 / (63 * (j : ℝ))) := neg_le_neg hfrac
    _ = -(u ^ 2) / (63 * (j : ℝ)) := by ring

private theorem ndFixedTotalSplitIndexPMF_map_headTotal_lowerTail_le
    (n j L : ℕ) (hn : 3 ≤ n) (hj : 1 ≤ j) (hjn : j < n)
    (hnL : n ≤ L) (hL3n : L ≤ 3 * n)
    (u : ℝ) (hu0 : 0 ≤ u) :
    (((ndFixedTotalSplitIndexPMF j (n - j) L
          (by omega) (by omega)).map
        (fun s => s.headTotal)).toOuterMeasure
      {m : ℕ |
        u ≤ (j : ℝ) * (L : ℝ) / (n : ℝ) - (m : ℝ)}).toReal ≤
      Real.exp (-(u ^ 2) / (63 * (j : ℝ))) := by
  letI : Fintype (NDFixedTotalSplitIndex j (n - j) L) :=
    ndFixedTotalSplitIndexFintypeOfLe j (n - j) L (by omega)
  let center : ℝ := (j : ℝ) * (L : ℝ) / (n : ℝ)
  let rho : ℝ :=
    (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ))
  rw [PMF.toOuterMeasure_map_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal]
  change Tao.pmfProb
      (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
      {s | u ≤ center - (s.headTotal : ℝ)} ≤
    Real.exp (-(u ^ 2) / (63 * (j : ℝ)))
  let q : ℕ := Nat.floor (center - u)
  have hjpos : 0 < j := by omega
  have htpos : 0 < n - j := Nat.sub_pos_of_lt hjn
  have hnR : 0 < (n : ℝ) := by positivity
  have hLR : 0 < (L : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < n) hnL)
  have hcenterLtL : center < (L : ℝ) := by
    have hjnR : (j : ℝ) < (n : ℝ) := by exact_mod_cast hjn
    dsimp [center]
    apply (div_lt_iff₀ hnR).2
    nlinarith [mul_lt_mul_of_pos_right hjnR hLR]
  have hcenter3j : center ≤ 3 * (j : ℝ) := by
    have hL3nR : (L : ℝ) ≤ 3 * (n : ℝ) := by
      exact_mod_cast hL3n
    have hj0R : 0 ≤ (j : ℝ) := by positivity
    dsimp [center]
    apply (div_le_iff₀ hnR).2
    nlinarith [mul_le_mul_of_nonneg_left hL3nR hj0R]
  rcases ndT3_ratio_bounds n j L hn hjn hnL hL3n with
    ⟨hrhoQuarter, _hcenterLower, hcenterUpper⟩
  change (1 : ℝ) / 4 ≤ rho at hrhoQuarter
  change center * rho ≤ (j : ℝ) at hcenterUpper
  have hrho0 : 0 ≤ rho := le_trans (by norm_num) hrhoQuarter
  by_cases hqj : q < j
  · have hempty :
        {s : NDFixedTotalSplitIndex j (n - j) L |
          u ≤ center - (s.headTotal : ℝ)} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hs
      have hsle : (s.headTotal : ℝ) ≤ center - u := by
        linarith
      have hheadq : s.headTotal ≤ q := by
        simpa [q] using Nat.le_floor hsle
      exact (not_le_of_gt hqj) (s.headLength_le.trans hheadq)
    rw [hempty, Tao.pmfProb_empty]
    exact Real.exp_nonneg _
  · have hjq : j ≤ q := Nat.le_of_not_gt hqj
    have hqpos : 0 < q := hjpos.trans_le hjq
    have hx1 : (1 : ℝ) ≤ center - u := by
      exact (Nat.floor_pos.mp (by simpa [q] using hqpos))
    have hx0 : 0 ≤ center - u := le_trans (by norm_num) hx1
    have hqle : (q : ℝ) ≤ center - u := by
      simpa [q] using Nat.floor_le hx0
    have hqLtLReal : (q : ℝ) < (L : ℝ) :=
      hqle.trans_lt ((sub_le_self center hu0).trans_lt hcenterLtL)
    have hqLtL : q < L := by exact_mod_cast hqLtLReal
    have hqL : q ≤ L - 1 := by omega
    have hq3jReal : (q : ℝ) ≤ 3 * (j : ℝ) :=
      hqle.trans ((sub_le_self center hu0).trans hcenter3j)
    have hq3j : q ≤ 3 * j := by exact_mod_cast hq3jReal
    have huRho : u / 4 ≤ u * rho := by
      calc
        u / 4 = u * ((1 : ℝ) / 4) := by ring
        _ ≤ u * rho := mul_le_mul_of_nonneg_left hrhoQuarter hu0
    have hqMean : (q : ℝ) * rho ≤ (j : ℝ) - u / 4 := by
      calc
        (q : ℝ) * rho ≤ (center - u) * rho :=
          mul_le_mul_of_nonneg_right hqle hrho0
        _ = center * rho - u * rho := by ring
        _ ≤ (j : ℝ) - u / 4 := by linarith
    have hlowerSubset :
        {s : NDFixedTotalSplitIndex j (n - j) L |
          u ≤ center - (s.headTotal : ℝ)} ⊆
        {s | s.headTotal ≤ q} := by
      intro s hs
      change u ≤ center - (s.headTotal : ℝ) at hs
      apply Nat.le_floor
      linarith
    have hmassRaw :=
      ndPmfProb_decideEvent_eq_of_map_eq
        (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
        (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
        (fun s => decide (s.headTotal ≤ q))
        (fun B => decide (j ≤ ndBarsPrefixCount B.1 q))
        (ndFixedTotalSplitIndexPMF_map_headTotal_le_eq_barsPrefixCount
          j (n - j) L q hjpos htpos (by omega))
        true
    have hmass :
        Tao.pmfProb
            (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
            {s | s.headTotal ≤ q} =
          Tao.pmfProb
            (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
            {B | j ≤ ndBarsPrefixCount B.1 q} := by
      simpa only [decide_eq_true_eq] using hmassRaw
    have hbarsSubset :
        {B : NDFixedTotalBars (j + (n - j)) L |
          j ≤ ndBarsPrefixCount B.1 q} ⊆
        {B | u / 4 ≤
          (ndBarsPrefixCount B.1 q : ℝ) - (q : ℝ) * rho} := by
      intro B hB
      change j ≤ ndBarsPrefixCount B.1 q at hB
      change u / 4 ≤
        (ndBarsPrefixCount B.1 q : ℝ) - (q : ℝ) * rho
      have hBcast : (j : ℝ) ≤ (ndBarsPrefixCount B.1 q : ℝ) := by
        exact_mod_cast hB
      linarith
    have htail := ndFixedTotalBarsPMF_prefixCount_upperTail_le
      (j + (n - j)) L q (by omega) (by omega)
        hqL hqpos (u / 4) (by positivity)
    have hrhoRaw :
        (((j + (n - j) - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) =
          rho := by
      dsimp [rho]
      rw [show j + (n - j) - 1 = n - 1 by omega]
    rw [hrhoRaw] at htail
    change Tao.pmfProb
        (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
        {B | u / 4 ≤
          (ndBarsPrefixCount B.1 q : ℝ) - (q : ℝ) * rho} ≤
      Real.exp (-2 * (u / 4) ^ 2 / (q : ℝ)) at htail
    calc
      Tao.pmfProb
          (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
          {s | u ≤ center - (s.headTotal : ℝ)} ≤
        Tao.pmfProb
          (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
          {s | s.headTotal ≤ q} :=
        Tao.pmfProb_mono _ hlowerSubset
      _ = Tao.pmfProb
          (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
          {B | j ≤ ndBarsPrefixCount B.1 q} := hmass
      _ ≤ Tao.pmfProb
          (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
          {B | u / 4 ≤
            (ndBarsPrefixCount B.1 q : ℝ) - (q : ℝ) * rho} :=
        Tao.pmfProb_mono _ hbarsSubset
      _ ≤ Real.exp (-2 * (u / 4) ^ 2 / (q : ℝ)) := htail
      _ ≤ Real.exp (-(u ^ 2) / (63 * (j : ℝ))) :=
        ndT3_lower_exp_le j q hjpos hqpos hq3j u

private theorem ndFixedTotalSplitIndexPMF_map_headTotal_upperTail_le
    (n j L : ℕ) (hn : 3 ≤ n) (hj : 1 ≤ j) (hjn : j < n)
    (hnL : n ≤ L) (hL3n : L ≤ 3 * n)
    (u : ℝ) (hu8 : 8 ≤ u) (hu3j : u ≤ 3 * (j : ℝ)) :
    (((ndFixedTotalSplitIndexPMF j (n - j) L
          (by omega) (by omega)).map
        (fun s => s.headTotal)).toOuterMeasure
      {m : ℕ |
        u ≤ (m : ℝ) - (j : ℝ) * (L : ℝ) / (n : ℝ)}).toReal ≤
      Real.exp (-(u ^ 2) / (63 * (j : ℝ))) := by
  letI : Fintype (NDFixedTotalSplitIndex j (n - j) L) :=
    ndFixedTotalSplitIndexFintypeOfLe j (n - j) L (by omega)
  let center : ℝ := (j : ℝ) * (L : ℝ) / (n : ℝ)
  let rho : ℝ :=
    (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ))
  rw [PMF.toOuterMeasure_map_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal]
  change Tao.pmfProb
      (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
      {s | u ≤ (s.headTotal : ℝ) - center} ≤
    Real.exp (-(u ^ 2) / (63 * (j : ℝ)))
  let z : ℝ := center + u
  let v : ℕ := Nat.ceil z
  have hjpos : 0 < j := by omega
  have htpos : 0 < n - j := Nat.sub_pos_of_lt hjn
  have hu0 : 0 ≤ u := by linarith
  have hnR : 0 < (n : ℝ) := by positivity
  have hcenter0 : 0 ≤ center := by
    dsimp [center]
    positivity
  have hz8 : (8 : ℝ) ≤ z := by
    dsimp [z]
    linarith
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz8
  have hzv : z ≤ (v : ℝ) := by
    simpa [v] using Nat.le_ceil z
  have hv8R : (8 : ℝ) ≤ (v : ℝ) := hz8.trans hzv
  have hv8 : 8 ≤ v := by exact_mod_cast hv8R
  have hvpos : 0 < v := by omega
  have hcenter3j : center ≤ 3 * (j : ℝ) := by
    have hL3nR : (L : ℝ) ≤ 3 * (n : ℝ) := by
      exact_mod_cast hL3n
    have hj0R : 0 ≤ (j : ℝ) := by positivity
    dsimp [center]
    apply (div_le_iff₀ hnR).2
    nlinarith [mul_le_mul_of_nonneg_left hL3nR hj0R]
  rcases ndT3_ratio_bounds n j L hn hjn hnL hL3n with
    ⟨hrhoQuarter, hcenterLower, _hcenterUpper⟩
  change (1 : ℝ) / 4 ≤ rho at hrhoQuarter
  change (j : ℝ) - 1 ≤ center * rho at hcenterLower
  have hrho0 : 0 ≤ rho := le_trans (by norm_num) hrhoQuarter
  have hupperToV :
      {s : NDFixedTotalSplitIndex j (n - j) L |
        u ≤ (s.headTotal : ℝ) - center} ⊆
      {s | v ≤ s.headTotal} := by
    intro s hs
    change u ≤ (s.headTotal : ℝ) - center at hs
    apply Nat.ceil_le.mpr
    change z ≤ (s.headTotal : ℝ)
    dsimp [z]
    linarith
  by_cases hvCut : v ≤ L - (n - j)
  · let q : ℕ := v - 1
    have hqpos : 0 < q := by
      dsimp [q]
      omega
    have hqL : q ≤ L - 1 := by
      dsimp [q]
      omega
    have hvcast : ((v - 1 : ℕ) : ℝ) = (v : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hqLower : z - 1 ≤ (q : ℝ) := by
      dsimp [q]
      rw [hvcast]
      linarith
    have hvlt : (v : ℝ) < z + 1 := by
      simpa [v] using Nat.ceil_lt_add_one hz0
    have hqz : (q : ℝ) < z := by
      dsimp [q]
      rw [hvcast]
      linarith
    have hz6j : z ≤ 6 * (j : ℝ) := by
      dsimp [z]
      linarith
    have hq6jReal : (q : ℝ) ≤ 6 * (j : ℝ) :=
      le_of_lt (hqz.trans_le hz6j)
    have hq6j : q ≤ 6 * j := by exact_mod_cast hq6jReal
    have hu1Rho : (u - 1) / 4 ≤ (u - 1) * rho := by
      have hu1 : 0 ≤ u - 1 := by linarith
      calc
        (u - 1) / 4 = (u - 1) * ((1 : ℝ) / 4) := by ring
        _ ≤ (u - 1) * rho :=
          mul_le_mul_of_nonneg_left hrhoQuarter hu1
    have hqMean :
        (j : ℝ) - 1 + (u - 1) / 4 ≤ (q : ℝ) * rho := by
      calc
        (j : ℝ) - 1 + (u - 1) / 4 ≤
            center * rho + (u - 1) * rho :=
          add_le_add hcenterLower hu1Rho
        _ = (z - 1) * rho := by
          dsimp [z]
          ring
        _ ≤ (q : ℝ) * rho :=
          mul_le_mul_of_nonneg_right hqLower hrho0
    have hupperSubset :
        {s : NDFixedTotalSplitIndex j (n - j) L |
          u ≤ (s.headTotal : ℝ) - center} ⊆
        {s | q < s.headTotal} := by
      intro s hs
      have hvs : v ≤ s.headTotal := hupperToV hs
      dsimp [q]
      omega
    have hmassRaw :=
      ndPmfProb_decideEvent_eq_of_map_eq
        (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
        (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
        (fun s => decide (s.headTotal ≤ q))
        (fun B => decide (j ≤ ndBarsPrefixCount B.1 q))
        (ndFixedTotalSplitIndexPMF_map_headTotal_le_eq_barsPrefixCount
          j (n - j) L q hjpos htpos (by omega))
        false
    have hmass :
        Tao.pmfProb
            (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
            {s | q < s.headTotal} =
          Tao.pmfProb
            (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
            {B | ndBarsPrefixCount B.1 q < j} := by
      simpa only [decide_eq_false_iff_not, not_le] using hmassRaw
    have hbarsSubset :
        {B : NDFixedTotalBars (j + (n - j)) L |
          ndBarsPrefixCount B.1 q < j} ⊆
        {B | (u - 1) / 4 ≤
          (q : ℝ) * rho - (ndBarsPrefixCount B.1 q : ℝ)} := by
      intro B hB
      change ndBarsPrefixCount B.1 q < j at hB
      change (u - 1) / 4 ≤
        (q : ℝ) * rho - (ndBarsPrefixCount B.1 q : ℝ)
      have hBnat : ndBarsPrefixCount B.1 q ≤ j - 1 := by omega
      have hBcast :
          (ndBarsPrefixCount B.1 q : ℝ) ≤ (j : ℝ) - 1 := by
        rw [show (j : ℝ) - 1 = ((j - 1 : ℕ) : ℝ) by
          rw [Nat.cast_sub (by omega)]; norm_num]
        exact_mod_cast hBnat
      linarith
    have htail := ndFixedTotalBarsPMF_prefixCount_lowerTail_le
      (j + (n - j)) L q (by omega) (by omega)
        hqL hqpos ((u - 1) / 4) (by nlinarith)
    have hrhoRaw :
        (((j + (n - j) - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) =
          rho := by
      dsimp [rho]
      rw [show j + (n - j) - 1 = n - 1 by omega]
    rw [hrhoRaw] at htail
    change Tao.pmfProb
        (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
        {B | (u - 1) / 4 ≤
          (q : ℝ) * rho - (ndBarsPrefixCount B.1 q : ℝ)} ≤
      Real.exp (-2 * ((u - 1) / 4) ^ 2 / (q : ℝ)) at htail
    calc
      Tao.pmfProb
          (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
          {s | u ≤ (s.headTotal : ℝ) - center} ≤
        Tao.pmfProb
          (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
          {s | q < s.headTotal} := Tao.pmfProb_mono _ hupperSubset
      _ = Tao.pmfProb
          (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
          {B | ndBarsPrefixCount B.1 q < j} := hmass
      _ ≤ Tao.pmfProb
          (ndFixedTotalBarsPMF (j + (n - j)) L (by omega) (by omega))
          {B | (u - 1) / 4 ≤
            (q : ℝ) * rho - (ndBarsPrefixCount B.1 q : ℝ)} :=
        Tao.pmfProb_mono _ hbarsSubset
      _ ≤ Real.exp (-2 * ((u - 1) / 4) ^ 2 / (q : ℝ)) := htail
      _ ≤ Real.exp (-(u ^ 2) / (63 * (j : ℝ))) :=
        ndT3_upper_exp_le j q hjpos hqpos hq6j u hu8
  · have hempty :
        {s : NDFixedTotalSplitIndex j (n - j) L |
          u ≤ (s.headTotal : ℝ) - center} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hs
      have hvs : v ≤ s.headTotal := hupperToV hs
      have hheadCut : s.headTotal ≤ L - (n - j) := by
        have htailLength := s.tailLength_le
        have htotal := s.total_eq
        omega
      exact hvCut (hvs.trans hheadCut)
    rw [hempty, Tao.pmfProb_empty]
    exact Real.exp_nonneg _

/-- Frozen-v10 T3: the conditioned split boundary has the stated two-sided
without-replacement tail, including both floor/ceiling boundary events. -/
theorem ndFixedTotalSplitIndexPMF_map_headTotal_absTail_le
    (n j L : ℕ) (hn : 3 ≤ n) (hj : 1 ≤ j) (hjn : j < n)
    (hnL : n ≤ L) (hL3n : L ≤ 3 * n)
    (u : ℝ) (hu8 : 8 ≤ u) (hu3j : u ≤ 3 * (j : ℝ)) :
    (((ndFixedTotalSplitIndexPMF j (n - j) L
          (by omega) (by omega)).map
        (fun s => s.headTotal)).toOuterMeasure
      {m : ℕ |
        u ≤ |(m : ℝ) - (j : ℝ) * (L : ℝ) / (n : ℝ)|}).toReal ≤
      2 * Real.exp (-(u ^ 2) / (63 * (j : ℝ))) := by
  letI : Fintype (NDFixedTotalSplitIndex j (n - j) L) :=
    ndFixedTotalSplitIndexFintypeOfLe j (n - j) L (by omega)
  let center : ℝ := (j : ℝ) * (L : ℝ) / (n : ℝ)
  have hlower := ndFixedTotalSplitIndexPMF_map_headTotal_lowerTail_le
    n j L hn hj hjn hnL hL3n u (by linarith)
  rw [PMF.toOuterMeasure_map_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal] at hlower
  change Tao.pmfProb
      (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
      {s | u ≤ center - (s.headTotal : ℝ)} ≤
    Real.exp (-(u ^ 2) / (63 * (j : ℝ))) at hlower
  have hupper := ndFixedTotalSplitIndexPMF_map_headTotal_upperTail_le
    n j L hn hj hjn hnL hL3n u hu8 hu3j
  rw [PMF.toOuterMeasure_map_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal] at hupper
  change Tao.pmfProb
      (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
      {s | u ≤ (s.headTotal : ℝ) - center} ≤
    Real.exp (-(u ^ 2) / (63 * (j : ℝ))) at hupper
  rw [PMF.toOuterMeasure_map_apply,
    ← Tao.pmfProb_eq_toOuterMeasure_toReal]
  change Tao.pmfProb
      (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
      {s | u ≤ |(s.headTotal : ℝ) - center|} ≤
    2 * Real.exp (-(u ^ 2) / (63 * (j : ℝ)))
  have hcover :
      {s : NDFixedTotalSplitIndex j (n - j) L |
        u ≤ |(s.headTotal : ℝ) - center|} ⊆
      {s | u ≤ center - (s.headTotal : ℝ)} ∪
        {s | u ≤ (s.headTotal : ℝ) - center} := by
    intro s hs
    change u ≤ |(s.headTotal : ℝ) - center| at hs
    rcases (le_abs.mp hs) with hupper' | hlower'
    · exact Set.mem_union_right _ hupper'
    · apply Set.mem_union_left
      change u ≤ center - (s.headTotal : ℝ)
      linarith
  calc
    Tao.pmfProb
        (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
        {s | u ≤ |(s.headTotal : ℝ) - center|} ≤
      Tao.pmfProb
        (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
        ({s | u ≤ center - (s.headTotal : ℝ)} ∪
          {s | u ≤ (s.headTotal : ℝ) - center}) :=
      Tao.pmfProb_mono _ hcover
    _ ≤ Tao.pmfProb
          (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
          {s | u ≤ center - (s.headTotal : ℝ)} +
        Tao.pmfProb
          (ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega))
          {s | u ≤ (s.headTotal : ℝ) - center} :=
      Tao.pmfProb_union_le_add _ _ _
    _ ≤ Real.exp (-(u ^ 2) / (63 * (j : ℝ))) +
        Real.exp (-(u ^ 2) / (63 * (j : ℝ))) :=
      add_le_add hlower hupper
    _ = 2 * Real.exp (-(u ^ 2) / (63 * (j : ℝ))) := by ring

end
end ND
end Erdos1135
