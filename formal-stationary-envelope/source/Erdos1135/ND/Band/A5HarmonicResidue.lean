import Erdos1135.ND.Band.A5BandPMF
import Erdos1135.Tao.Probability.LogWindowOddNatPoint

/-!
# Exact-Band Harmonic Source Residues

This leaf identifies the exact A5 harmonic band law with Tao's inclusive
odd-window law, then applies the width-free logarithmic residue estimate at
the Section 5 exponent.  The independent A5 mass floor replaces the
factor-two window-width premise used by Tao's scheduled corollary.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Native point mass of the mapped harmonic band law on its exact support. -/
theorem ndA5HarmonicBandPMF_apply_of_mem
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (N : Tao.TaoOddNat) (hN : N.1 ∈ ndA5OddBand B branch j) :
    ndA5HarmonicBandPMF B branch j hB hcount N =
      ENNReal.ofReal
        (Tao.logNatWeight N.1 /
          Tao.logFinsetMass (ndA5OddBand B branch j)) := by
  classical
  let Nband : NDA5BandCarrier B branch j := ⟨N.1, hN⟩
  have hmap : N = ndA5BandValueToOddNat Nband := by
    apply Subtype.ext
    rfl
  rw [ndA5HarmonicBandPMF, PMF.map_apply]
  rw [tsum_eq_single Nband]
  · rw [if_pos hmap]
    rw [ndA5HarmonicBandCarrierPMF, Tao.logFinsetPMF,
      PMF.ofFintype_apply]
  · intro a ha
    rw [if_neg]
    intro hEq
    apply ha
    apply Subtype.ext
    have hval := congrArg Subtype.val hEq
    simpa only [ndA5BandValueToOddNat, Nband] using hval.symm

/-- The mapped harmonic band law vanishes off its exact support. -/
theorem ndA5HarmonicBandPMF_apply_eq_zero_of_not_mem
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (N : Tao.TaoOddNat) (hN : N.1 ∉ ndA5OddBand B branch j) :
    ndA5HarmonicBandPMF B branch j hB hcount N = 0 := by
  classical
  rw [ndA5HarmonicBandPMF, PMF.map_apply, ENNReal.tsum_eq_zero]
  intro a
  have hne : N ≠ ndA5BandValueToOddNat a := by
    intro hEq
    apply hN
    have hval := congrArg Subtype.val hEq
    simpa only [ndA5BandValueToOddNat, hval] using a.2
  simp only [if_neg hne]

/-- Totalized real point formula for the exact harmonic band law. -/
theorem ndA5HarmonicBandPMF_apply_toReal
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch} {j : ℕ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (N : Tao.TaoOddNat) :
    (ndA5HarmonicBandPMF B branch j hB hcount N).toReal =
      if N.1 ∈ ndA5OddBand B branch j then
        Tao.logNatWeight N.1 /
          Tao.logFinsetMass (ndA5OddBand B branch j)
      else 0 := by
  classical
  by_cases hN : N.1 ∈ ndA5OddBand B branch j
  · rw [if_pos hN, ndA5HarmonicBandPMF_apply_of_mem hB hcount N hN]
    exact ENNReal.toReal_ofReal
      (div_nonneg (Tao.logNatWeight_nonneg N.1)
        (logFinsetMass_ndA5OddBand_pos hB j hcount).le)
  · rw [if_neg hN,
      ndA5HarmonicBandPMF_apply_eq_zero_of_not_mem hB hcount N hN]
    rfl

/-- The exact half-open A5 harmonic law is Tao's inclusive odd-window law at
`lo = ceil z` and `hi = ceil u - 1`. -/
theorem ndA5HarmonicBandPMF_eq_oddLogWindowOddNatPMF
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch}
    (j : ℕ) (hcount : 0 < ndA5BandCount B branch)
    (hmass : 0 < Tao.logFinsetMass
      (Tao.oddLogWindow
        (Nat.ceil (ndA5BandLower B branch j))
        (Nat.ceil (ndA5BandLower B branch (j + 1)) - 1))) :
    ndA5HarmonicBandPMF B branch j hB hcount =
      Tao.oddLogWindowOddNatPMF
        (Nat.ceil (ndA5BandLower B branch j))
        (Nat.ceil (ndA5BandLower B branch (j + 1)) - 1) hmass := by
  apply PMF.ext
  intro N
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ N) (PMF.apply_ne_top _ N)).mp
  rw [ndA5HarmonicBandPMF_apply_toReal hB hcount,
    Tao.oddLogWindowOddNatPMF_apply_toReal,
    ndA5OddBand_eq_oddLogWindow hB j hcount]

/-- Every A5 lower endpoint lies above its branch source scale. -/
theorem taoSection5SourceY_le_ndA5BandLower
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    Tao.taoSection5SourceY B branch ≤ ndA5BandLower B branch j := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  have hexp :
      1 ≤ Real.exp ((j : ℝ) * ndA5BandBeta B branch) :=
    Real.one_le_exp
      (mul_nonneg (Nat.cast_nonneg j) (ndA5BandBeta_nonneg hB branch))
  unfold ndA5BandLower
  simpa using mul_le_mul_of_nonneg_left hexp hYpos.le

/-- The Section 5 quadratic modulus room reaches every exact A5 band. -/
theorem taoSection5NPrime_sq_pow_le_ceil_ndA5BandLower
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) (j : ℕ) :
    (2 ^ Tao.taoSection5NPrime B) ^ 2 ≤
      Nat.ceil (ndA5BandLower B branch j) := by
  have hsource := Tao.taoSection5Threshold_le_sourceLo hB branch
  have hceil :
      Tao.taoSection5SourceLo B branch ≤
        Nat.ceil (ndA5BandLower B branch j) := by
    simpa [Tao.taoSection5SourceLo, Tao.taoNyLo] using
      Nat.ceil_le_ceil (taoSection5SourceY_le_ndA5BandLower hB branch j)
  exact (Tao.taoSection5NPrime_sq_pow_le_threshold hB).trans
    (hsource.trans hceil)

/-- Exact-band harmonic source residues satisfy the fixed full-L1
`2 * 2^(-M)` estimate at `M = 3*n0`, without a factor-two band-width
hypothesis. -/
theorem taoTV_ndA5HarmonicBandPMF_sourceResidue_canonical_le
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch}
    (j : ℕ) (hcount : 0 < ndA5BandCount B branch)
    (hM : 1 ≤ Tao.taoSection5NPrime B) :
    Tao.taoTV
        (Tao.taoProp19SourceResidueLaw
          (ndA5HarmonicBandPMF B branch j hB hcount)
          (Tao.taoSection5NPrime B))
        (Tao.taoCanonicalUniformOddResiduePMF
          (Tao.taoSection5NPrime B)) ≤
      2 * ((2 : ℝ) ^ (-(Tao.taoSection5NPrime B : ℝ))) := by
  let lo := Nat.ceil (ndA5BandLower B branch j)
  let hi := Nat.ceil (ndA5BandLower B branch (j + 1)) - 1
  let M := Tao.taoSection5NPrime B
  let H := Tao.logFinsetMass (Tao.oddLogWindow lo hi)
  let K := M - 1
  have hlo : 1 ≤ lo := by
    have hz := six_le_ndA5BandLower hB j hcount
    have hceil :
        (1 : ℝ) ≤ (Nat.ceil (ndA5BandLower B branch j) : ℕ) :=
      (by linarith : (1 : ℝ) ≤ ndA5BandLower B branch j).trans
        (Nat.le_ceil _)
    dsimp [lo]
    exact_mod_cast hceil
  have hlohi : lo ≤ hi := by
    have hceil := ndA5BandLower_ceil_lt_ceil_succ hB j hcount
    dsimp [lo, hi]
    omega
  have hband :
      ndA5OddBand B branch j = Tao.oddLogWindow lo hi := by
    simpa only [lo, hi] using ndA5OddBand_eq_oddLogWindow hB j hcount
  have hmass : 0 < H := by
    dsimp [H]
    rw [← hband]
    exact logFinsetMass_ndA5OddBand_pos hB j hcount
  have hmassQuarter : (1 / 4 : ℝ) ≤ H := by
    dsimp [H]
    rw [← hband]
    exact one_fourth_le_logFinsetMass_ndA5OddBand hB j hcount
  have hKM : K + 1 = M := by
    dsimp [K, M]
    omega
  have hfinite :=
    Tao.taoTV_oddLogWindow_sourceResidue_canonical_le
      hlo hlohi hmass K
  rw [hKM] at hfinite
  have hpmf :
      ndA5HarmonicBandPMF B branch j hB hcount =
        Tao.oddLogWindowOddNatPMF lo hi hmass := by
    simpa only [lo, hi] using
      ndA5HarmonicBandPMF_eq_oddLogWindowOddNatPMF
        hB j hcount hmass
  rw [← hpmf] at hfinite
  let A : ℝ := ((2 ^ (M - 1) : ℕ) : ℝ)
  let Q : ℝ := ((2 ^ M : ℕ) : ℝ)
  let L : ℝ := lo
  have hfinite' :
      Tao.taoTV
          (Tao.taoProp19SourceResidueLaw
            (ndA5HarmonicBandPMF B branch j hB hcount) M)
          (Tao.taoCanonicalUniformOddResiduePMF M) ≤
        A / (L * H) := by
    simpa [K, A, L, H] using hfinite
  have hQpos : 0 < Q := by positivity
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast (show 0 < lo by omega)
  have hdenpos : 0 < L * H := mul_pos hLpos hmass
  have hAeq : A = Q / 2 := by
    have hpow := pow_sub_one_mul (Nat.ne_of_gt (show 0 < M by
      dsimp [M]
      omega)) 2
    have hpowReal := congrArg (fun n : ℕ => (n : ℝ)) hpow
    dsimp [A, Q]
    norm_num at hpowReal ⊢
    linarith
  have hroom : (2 ^ M) ^ 2 ≤ lo := by
    dsimp [M, lo]
    exact taoSection5NPrime_sq_pow_le_ceil_ndA5BandLower hB branch j
  have hroomReal : Q ^ 2 ≤ L := by
    dsimp [Q, L]
    exact_mod_cast hroom
  have hLH : Q ^ 2 / 4 ≤ L * H := by
    calc
      Q ^ 2 / 4 ≤ L / 4 :=
        div_le_div_of_nonneg_right hroomReal (by norm_num)
      _ = L * (1 / 4 : ℝ) := by ring
      _ ≤ L * H := mul_le_mul_of_nonneg_left hmassQuarter hLpos.le
  have hscalar : A / (L * H) ≤ 2 / Q := by
    apply (div_le_div_iff₀ hdenpos hQpos).2
    rw [hAeq]
    nlinarith
  calc
    Tao.taoTV
        (Tao.taoProp19SourceResidueLaw
          (ndA5HarmonicBandPMF B branch j hB hcount)
          (Tao.taoSection5NPrime B))
        (Tao.taoCanonicalUniformOddResiduePMF
          (Tao.taoSection5NPrime B)) ≤ A / (L * H) := by
            simpa [M] using hfinite'
    _ ≤ 2 / Q := hscalar
    _ = 2 * ((2 : ℝ) ^ (-(Tao.taoSection5NPrime B : ℝ))) := by
      dsimp [Q, M]
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_natCast]
      norm_num [div_eq_mul_inv]

end

end ND
end Erdos1135
