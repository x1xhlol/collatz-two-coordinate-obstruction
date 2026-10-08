import Erdos1135.Tao.Fourier.Lemma74SoutheastTransport

set_option autoImplicit false

namespace Erdos1135.Tao

noncomputable def integerHeightTrap (a : TaoSection7Point) (h : ℕ) : TaoSection7Triangle :=
  ⟨a.j, a.l, (h : ℝ) * Real.log 2⟩

theorem integerHeightTrap_downN_mem (a : TaoSection7Point) {h k : ℕ} (hk : k ≤ h) :
    (integerHeightTrap a h).Mem (a.downN k) := by
  refine ⟨le_rfl, ?_, ?_⟩
  · simp [integerHeightTrap, TaoSection7Point.downN]
  · simpa [integerHeightTrap, TaoSection7Triangle.horizontalDepth,
      TaoSection7Triangle.verticalDepth, TaoSection7Point.downN] using
      mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ h by exact_mod_cast hk)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem sourceTheta_downN_eq_of_black_column
    (n : ℕ) (xi : ZMod (3 ^ n)) (a : TaoSection7Point) (h : ℕ)
    {epsilon : ℝ} (hepsilon : epsilon < 1 / 4)
    (hblack : ∀ k ≤ h, taoSection7SourceBlackPoint n xi epsilon (a.downN k)) :
    taoSection7SourceTheta n xi (a.downN h) =
      (2 : ℝ) ^ h * taoSection7SourceTheta n xi a := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hcol : ∀ k ≤ h, taoSection7SourceBlackPoint n xi epsilon (a.downN k) :=
      fun k hk => hblack k (by omega)
    have hb : |taoSection7SourceTheta n xi (a.downN h)| ≤ epsilon := hcol h le_rfl
    have hguard : |2 * taoSection7SourceTheta n xi (a.downN h)| < (1 / 2 : ℝ) := by
      rw [abs_mul]
      norm_num
      linarith
    rw [TaoSection7Point.downN_succ,
      taoSection7SourceTheta_down_of_abs_lt_half n xi (a.downN h) hguard,
      ih hcol, pow_succ]
    ring

theorem integerHeightTrap_black_iff_top_small
    (n : ℕ) (xi : ZMod (3 ^ n)) (a : TaoSection7Point) (h : ℕ)
    {epsilon : ℝ} (hepsilon : epsilon < 1 / 4) :
    (integerHeightTrap a h).BlackOn (taoSection7SourceBlackPoint n xi epsilon) ↔
      |taoSection7SourceTheta n xi a| ≤ epsilon / (2 : ℝ) ^ h := by
  have hpow : (0 : ℝ) < 2 ^ h := by positivity
  constructor
  · intro hb
    have hcol : ∀ k ≤ h, taoSection7SourceBlackPoint n xi epsilon (a.downN k) :=
      fun k hk => hb _ (integerHeightTrap_downN_mem a hk)
    have hend : |taoSection7SourceTheta n xi (a.downN h)| ≤ epsilon := hcol h le_rfl
    rw [sourceTheta_downN_eq_of_black_column n xi a h hepsilon hcol,
      abs_mul, abs_of_pos hpow] at hend
    exact (le_div_iff₀ hpow).mpr (by nlinarith)
  · intro htop q hq
    change |taoSection7SourceTheta n xi q| ≤ epsilon
    have hj : (a.j : ℕ) ≤ q.j := hq.1
    have hl : q.l ≤ a.l := hq.2.1
    have hv : ((taoSection7SoutheastV a q : ℕ) : ℝ) = ((a.l - q.l : ℤ) : ℝ) := by
      exact_mod_cast taoSection7SoutheastV_intCast a q hl
    have hweight : taoSection7SoutheastWeight a q ≤ (h : ℝ) * Real.log 2 := by
      unfold taoSection7SoutheastWeight
      rw [hv]
      exact hq.2.2
    have hexp : Real.exp (taoSection7SoutheastWeight a q) ≤ (2 : ℝ) ^ h := by
      have hb := Real.exp_le_exp.mpr hweight
      simpa [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hb
    calc
      |taoSection7SourceTheta n xi q| ≤
          Real.exp (taoSection7SoutheastWeight a q) * |taoSection7SourceTheta n xi a| :=
        abs_taoSection7SourceTheta_southeast_le n xi a q hj hl
      _ ≤ 2 ^ h * |taoSection7SourceTheta n xi a| :=
        mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
      _ ≤ epsilon := by
        have hb := (le_div_iff₀ hpow).mp htop
        nlinarith

end Erdos1135.Tao

#print axioms Erdos1135.Tao.integerHeightTrap_black_iff_top_small
