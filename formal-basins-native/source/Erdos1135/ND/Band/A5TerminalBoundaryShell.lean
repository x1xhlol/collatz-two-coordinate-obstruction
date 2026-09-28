import Erdos1135.ND.Band.A5BandNormalizer

/-!
# A5 Terminal Boundary Shells

This leaf charges the once-only affine-position mismatch at the two physical
endpoints of one exact A5 band.  The lower shell is a half-open overcover of
the genuinely open nominal-only strip; the upper shell has the exact
closed/open convention of the physical-only strip.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The source-space thickness of the terminal affine boundary strips. -/
noncomputable def ndA5TerminalBoundaryEpsilon (B : ℕ) : ℝ :=
  (B : ℝ) ^ (-(9 / 10 : ℝ))

/-- The nominal-only strip immediately below the physical lower endpoint. -/
noncomputable def ndA5LowerTerminalBoundaryShell
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) : Finset ℕ :=
  oddHalfOpenRealWindow
    (ndA5BandLower B branch j *
      Real.exp (-ndA5TerminalBoundaryEpsilon B))
    (ndA5BandLower B branch j)

/-- The physical-only strip immediately below the physical upper endpoint. -/
noncomputable def ndA5UpperTerminalBoundaryShell
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) : Finset ℕ :=
  oddHalfOpenRealWindow
    (ndA5BandLower B branch (j + 1) *
      Real.exp (-ndA5TerminalBoundaryEpsilon B))
    (ndA5BandLower B branch (j + 1))

theorem ndA5TerminalBoundaryEpsilon_pos
    {B : ℕ} (hB : 1 ≤ B) :
    0 < ndA5TerminalBoundaryEpsilon B := by
  unfold ndA5TerminalBoundaryEpsilon
  exact Real.rpow_pos_of_pos (by exact_mod_cast hB) _

theorem ndA5TerminalBoundaryEpsilon_le_one
    {B : ℕ} (hB : 1 ≤ B) :
    ndA5TerminalBoundaryEpsilon B ≤ 1 := by
  unfold ndA5TerminalBoundaryEpsilon
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hB) (by norm_num)

/-- Flat size of one multiplicative shell, including both ceiling errors. -/
theorem card_oddHalfOpenRealWindow_mul_exp_neg_lt
    {x eps : ℝ} (hx : 0 < x) (heps : 0 ≤ eps) :
    ((oddHalfOpenRealWindow (x * Real.exp (-eps)) x).card : ℝ) <
      x * eps / 2 + 1 := by
  have hexpLe : Real.exp (-eps) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr heps)
  have hlower0 : 0 ≤ x * Real.exp (-eps) :=
    mul_nonneg hx.le (Real.exp_pos _).le
  have hlowerLe : x * Real.exp (-eps) ≤ x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexpLe hx.le
  have hcard :=
    abs_card_oddHalfOpenRealWindow_sub_half_width_lt_one
      hlower0 hlowerLe
  have hwidth : x - x * Real.exp (-eps) ≤ x * eps := by
    have h := Real.one_sub_le_exp_neg eps
    have hmul := mul_le_mul_of_nonneg_left h hx.le
    nlinarith
  rw [abs_lt] at hcard
  linarith

/-- Harmonic size of one multiplicative shell before its rounding term is
absorbed into the base scale. -/
theorem logFinsetMass_oddHalfOpenRealWindow_mul_exp_neg_le
    {x eps : ℝ} (hx : 0 < x) (heps : 0 ≤ eps) :
    Tao.logFinsetMass
        (oddHalfOpenRealWindow (x * Real.exp (-eps)) x) ≤
      eps / 2 + 3 / (2 * (x * Real.exp (-eps))) := by
  have hlowerPos : 0 < x * Real.exp (-eps) :=
    mul_pos hx (Real.exp_pos _)
  have hexpLe : Real.exp (-eps) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr heps)
  have hlowerLe : x * Real.exp (-eps) ≤ x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexpLe hx.le
  calc
    Tao.logFinsetMass
        (oddHalfOpenRealWindow (x * Real.exp (-eps)) x) ≤
        (1 / 2 : ℝ) *
            (Real.log x - Real.log (x * Real.exp (-eps))) +
          3 / (2 * (x * Real.exp (-eps))) :=
      logFinsetMass_oddHalfOpenRealWindow_le_half_log_width_add_three_div
        hlowerPos hlowerLe
    _ = eps / 2 + 3 / (2 * (x * Real.exp (-eps))) := by
      rw [Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp]
      ring

private theorem three_div_two_mul_exp_neg_le_nine_div_two_mul
    {b x eps : ℝ} (hb : 0 < b) (hbx : b ≤ x)
    (heps : eps ≤ 1) :
    3 / (2 * (x * Real.exp (-eps))) ≤ 9 / (2 * b) := by
  have hthird : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    have hdecimal := Real.exp_neg_one_gt_d9
    norm_num at hdecimal ⊢
    linarith
  have hneg : (-1 : ℝ) ≤ -eps := by linarith
  have hexp : (1 / 3 : ℝ) ≤ Real.exp (-eps) :=
    hthird.trans (Real.exp_monotone hneg)
  have hx : 0 < x := hb.trans_le hbx
  have hlower : b / 3 ≤ x * Real.exp (-eps) := by
    have h1 : b * (1 / 3 : ℝ) ≤ x * (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hbx (by norm_num)
    have h2 : x * (1 / 3 : ℝ) ≤ x * Real.exp (-eps) :=
      mul_le_mul_of_nonneg_left hexp hx.le
    nlinarith
  have hinv :
      1 / (x * Real.exp (-eps)) ≤ 1 / (b / 3) :=
    one_div_le_one_div_of_le (div_pos hb (by norm_num)) hlower
  calc
    3 / (2 * (x * Real.exp (-eps))) =
        (3 / 2 : ℝ) * (1 / (x * Real.exp (-eps))) := by
      field_simp
    _ ≤ (3 / 2 : ℝ) * (1 / (b / 3)) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 9 / (2 * b) := by field_simp; norm_num

theorem logFinsetMass_ndA5LowerTerminalBoundaryShell_le
    {B : ℕ} (hB : 1 ≤ B)
    (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    Tao.logFinsetMass (ndA5LowerTerminalBoundaryShell B branch j) ≤
      ndA5TerminalBoundaryEpsilon B / 2 + 9 / (2 * (B : ℝ)) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hx : 0 < ndA5BandLower B branch j :=
    hBpos.trans_le (cast_le_ndA5BandLower hB branch j)
  have hraw := logFinsetMass_oddHalfOpenRealWindow_mul_exp_neg_le
    hx (ndA5TerminalBoundaryEpsilon_pos hB).le
  have hround := three_div_two_mul_exp_neg_le_nine_div_two_mul
    hBpos (cast_le_ndA5BandLower hB branch j)
    (ndA5TerminalBoundaryEpsilon_le_one hB)
  unfold ndA5LowerTerminalBoundaryShell
  linarith

theorem logFinsetMass_ndA5UpperTerminalBoundaryShell_le
    {B : ℕ} (hB : 1 ≤ B)
    (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    Tao.logFinsetMass (ndA5UpperTerminalBoundaryShell B branch j) ≤
      ndA5TerminalBoundaryEpsilon B / 2 + 9 / (2 * (B : ℝ)) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hx : 0 < ndA5BandLower B branch (j + 1) :=
    hBpos.trans_le (cast_le_ndA5BandLower hB branch (j + 1))
  have hraw := logFinsetMass_oddHalfOpenRealWindow_mul_exp_neg_le
    hx (ndA5TerminalBoundaryEpsilon_pos hB).le
  have hround := three_div_two_mul_exp_neg_le_nine_div_two_mul
    hBpos (cast_le_ndA5BandLower hB branch (j + 1))
    (ndA5TerminalBoundaryEpsilon_le_one hB)
  unfold ndA5UpperTerminalBoundaryShell
  linarith

private theorem two_le_exp_ndA5BandBeta
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    (hcount : 0 < ndA5BandCount B branch) :
    (2 : ℝ) ≤ Real.exp (ndA5BandBeta B branch) := by
  have hbeta : (1 : ℝ) ≤ ndA5BandBeta B branch :=
    (ndA5BandBeta_mem_Ico hcount).1
  have h := Real.add_one_le_exp (ndA5BandBeta B branch)
  linarith

private theorem card_ndA5BoundaryShellUnion_lt
    {B : ℕ} (hB : 1 ≤ B)
    {branch : Tao.TaoSection5SourceBranch} (j : ℕ) :
    (((ndA5LowerTerminalBoundaryShell B branch j ∪
          ndA5UpperTerminalBoundaryShell B branch j).card : ℕ) : ℝ) <
      ndA5BandLower B branch j *
          (1 + Real.exp (ndA5BandBeta B branch)) *
          ndA5TerminalBoundaryEpsilon B / 2 + 2 := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hz : 0 < ndA5BandLower B branch j :=
    hBpos.trans_le (cast_le_ndA5BandLower hB branch j)
  have hu : 0 < ndA5BandLower B branch (j + 1) :=
    hBpos.trans_le (cast_le_ndA5BandLower hB branch (j + 1))
  have heps := ndA5TerminalBoundaryEpsilon_pos hB
  have hlo := card_oddHalfOpenRealWindow_mul_exp_neg_lt hz heps.le
  have hhi := card_oddHalfOpenRealWindow_mul_exp_neg_lt hu heps.le
  have hunionNat := Finset.card_union_le
    (ndA5LowerTerminalBoundaryShell B branch j)
    (ndA5UpperTerminalBoundaryShell B branch j)
  have hunion :
      (((ndA5LowerTerminalBoundaryShell B branch j ∪
          ndA5UpperTerminalBoundaryShell B branch j).card : ℕ) : ℝ) ≤
        (ndA5LowerTerminalBoundaryShell B branch j).card +
          (ndA5UpperTerminalBoundaryShell B branch j).card := by
    exact_mod_cast hunionNat
  unfold ndA5LowerTerminalBoundaryShell at hlo
  unfold ndA5UpperTerminalBoundaryShell at hhi
  unfold ndA5LowerTerminalBoundaryShell ndA5UpperTerminalBoundaryShell at hunion ⊢
  rw [ndA5BandLower_succ] at hhi hunion ⊢
  nlinarith

private theorem third_band_width_lt_card_ndA5OddBand
    {B : ℕ} (hB : 1 ≤ B)
    {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    ndA5BandLower B branch j *
        (Real.exp (ndA5BandBeta B branch) - 1) / 3 <
      ((ndA5OddBand B branch j).card : ℝ) := by
  have hzSix := six_le_ndA5BandLower hB j hcount
  have hrTwo := two_le_exp_ndA5BandBeta hcount
  have hwidth :
      6 ≤ ndA5BandLower B branch j *
        (Real.exp (ndA5BandBeta B branch) - 1) := by
    have hone : (1 : ℝ) ≤ Real.exp (ndA5BandBeta B branch) - 1 := by
      linarith
    exact hzSix.trans
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hone (by linarith :
          0 ≤ ndA5BandLower B branch j))
  have hcard := abs_card_ndA5OddBand_sub_flat_center_lt_one
    hB j hcount
  rw [abs_lt] at hcard
  linarith

/-- Fixed-band flat boundary charge.  The union is used only to avoid double
charging a possible overlap; no shell-disjointness premise is needed. -/
theorem ndA5FlatBoundaryShellRatio_lt_eleven_rpow_neg_nine_tenths
    {B : ℕ} (hB : 1 ≤ B)
    {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    (((ndA5LowerTerminalBoundaryShell B branch j ∪
          ndA5UpperTerminalBoundaryShell B branch j).card : ℝ) /
        ((ndA5OddBand B branch j).card : ℝ)) <
      11 * (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
  let z := ndA5BandLower B branch j
  let r := Real.exp (ndA5BandBeta B branch)
  let eps := ndA5TerminalBoundaryEpsilon B
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hz : 0 < z := by
    exact hBpos.trans_le (cast_le_ndA5BandLower hB branch j)
  have heps : 0 < eps := ndA5TerminalBoundaryEpsilon_pos hB
  have hr : (2 : ℝ) ≤ r := two_le_exp_ndA5BandBeta hcount
  have hnum := card_ndA5BoundaryShellUnion_lt
    (branch := branch) hB j
  have hden := third_band_width_lt_card_ndA5OddBand hB j hcount
  have hdenPos : (0 : ℝ) < (ndA5OddBand B branch j).card := by
    exact_mod_cast ndA5OddBand_card_pos hB j hcount
  have htargetPos : 0 < (9 / 2 : ℝ) * eps + 6 / z := by positivity
  have hmargin :
      z * (1 + r) * eps / 2 + 2 ≤
        (z * (r - 1) / 3) * ((9 / 2 : ℝ) * eps + 6 / z) := by
    have hnonneg : 0 ≤ (r - 2) * (z * eps + 2) :=
      mul_nonneg (sub_nonneg.mpr hr)
        (add_nonneg (mul_nonneg hz.le heps.le) (by norm_num))
    have heq :
        (z * (r - 1) / 3) * ((9 / 2 : ℝ) * eps + 6 / z) -
            (z * (1 + r) * eps / 2 + 2) =
          (r - 2) * (z * eps + 2) := by
      field_simp [hz.ne']
      ring
    linarith
  have hratio :
      (((ndA5LowerTerminalBoundaryShell B branch j ∪
            ndA5UpperTerminalBoundaryShell B branch j).card : ℝ) /
          ((ndA5OddBand B branch j).card : ℝ)) <
        (9 / 2 : ℝ) * eps + 6 / z := by
    apply (div_lt_iff₀ hdenPos).2
    change
      (((ndA5LowerTerminalBoundaryShell B branch j ∪
            ndA5UpperTerminalBoundaryShell B branch j).card : ℕ) : ℝ) < _
    have hmul := mul_lt_mul_of_pos_right hden htargetPos
    dsimp only [z, r, eps] at hnum hden hmul ⊢
    linarith
  have hinvZB : 1 / z ≤ 1 / (B : ℝ) :=
    one_div_le_one_div_of_le hBpos (by
      simpa only [z] using cast_le_ndA5BandLower hB branch j)
  have hinvBEps : 1 / (B : ℝ) ≤ eps := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hBreal
      (by norm_num : (-1 : ℝ) ≤ -(9 / 10 : ℝ))
    rw [Real.rpow_neg_one] at hpow
    simpa only [eps, ndA5TerminalBoundaryEpsilon, one_div] using hpow
  have htarget :
      (9 / 2 : ℝ) * eps + 6 / z < 11 * eps := by
    have hinv : 1 / z ≤ eps := hinvZB.trans hinvBEps
    have hSix : 6 / z ≤ 6 * eps := by
      calc
        6 / z = 6 * (1 / z) := by ring
        _ ≤ 6 * eps := mul_le_mul_of_nonneg_left hinv (by norm_num)
    nlinarith
  simpa only [eps, ndA5TerminalBoundaryEpsilon] using hratio.trans htarget

private theorem thirty_six_div_cast_le_boundaryEpsilon
    {B : ℕ} (hB : 1 ≤ B)
    (hlogB : (300000 : ℝ) ≤ Real.log B) :
    36 / (B : ℝ) ≤ ndA5TerminalBoundaryEpsilon B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have h36pow : (36 : ℝ) ≤ (B : ℝ) ^ (1 / 10 : ℝ) := by
    calc
      (36 : ℝ) ≤ Real.log B * (1 / 10 : ℝ) + 1 := by
        nlinarith
      _ ≤ Real.exp (Real.log B * (1 / 10 : ℝ)) :=
        Real.add_one_le_exp _
      _ = (B : ℝ) ^ (1 / 10 : ℝ) := by
        rw [Real.rpow_def_of_pos hBpos]
  calc
    36 / (B : ℝ) ≤ (B : ℝ) ^ (1 / 10 : ℝ) / (B : ℝ) :=
      div_le_div_of_nonneg_right h36pow hBpos.le
    _ = (B : ℝ) ^ ((1 / 10 : ℝ) - 1) := by
      rw [Real.rpow_sub hBpos, Real.rpow_one]
    _ = (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
      norm_num
    _ = ndA5TerminalBoundaryEpsilon B := rfl

/-- Fixed-band harmonic boundary charge, normalized by the exact physical
band mass. -/
theorem ndA5HarmonicBoundaryShellRatio_le_five_rpow_neg_nine_tenths
    {B : ℕ} (hB : 1 ≤ B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    {branch : Tao.TaoSection5SourceBranch} (j : ℕ)
    (hcount : 0 < ndA5BandCount B branch) :
    (Tao.logFinsetMass (ndA5LowerTerminalBoundaryShell B branch j) +
        Tao.logFinsetMass (ndA5UpperTerminalBoundaryShell B branch j)) /
        Tao.logFinsetMass (ndA5OddBand B branch j) ≤
      5 * (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
  let eps := ndA5TerminalBoundaryEpsilon B
  let shellMass :=
    Tao.logFinsetMass (ndA5LowerTerminalBoundaryShell B branch j) +
      Tao.logFinsetMass (ndA5UpperTerminalBoundaryShell B branch j)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hshell0 : 0 ≤ shellMass := by
    dsimp only [shellMass]
    exact add_nonneg (Tao.logFinsetMass_nonneg _)
      (Tao.logFinsetMass_nonneg _)
  have hshell : shellMass ≤ eps + 9 / (B : ℝ) := by
    have hlo := logFinsetMass_ndA5LowerTerminalBoundaryShell_le
      hB branch j
    have hhi := logFinsetMass_ndA5UpperTerminalBoundaryShell_le
      hB branch j
    calc
      shellMass ≤
          (ndA5TerminalBoundaryEpsilon B / 2 + 9 / (2 * (B : ℝ))) +
            (ndA5TerminalBoundaryEpsilon B / 2 + 9 / (2 * (B : ℝ))) :=
        add_le_add hlo hhi
      _ = eps + 9 / (B : ℝ) := by dsimp only [eps]; ring
  have hfloor := one_fourth_le_logFinsetMass_ndA5OddBand hB j hcount
  have hdenPos := logFinsetMass_ndA5OddBand_pos hB j hcount
  have h36 := thirty_six_div_cast_le_boundaryEpsilon hB hlogB
  change shellMass / Tao.logFinsetMass (ndA5OddBand B branch j) ≤ _
  calc
    shellMass / Tao.logFinsetMass (ndA5OddBand B branch j) ≤
        shellMass / (1 / 4 : ℝ) :=
      div_le_div_of_nonneg_left hshell0 (by norm_num) hfloor
    _ = 4 * shellMass := by ring
    _ ≤ 4 * (eps + 9 / (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hshell (by norm_num)
    _ = 4 * eps + 36 / (B : ℝ) := by ring
    _ ≤ 5 * eps := by linarith
    _ = 5 * (B : ℝ) ^ (-(9 / 10 : ℝ)) := rfl

end

end ND
end Erdos1135
