import Erdos1135.Tao.Probability.LogWindowFloorPerturbation
import Erdos1135.Tao.Probability.ReciprocalProgression
import Mathlib.Data.Int.CardIntervalMod

/-!
# Sharp Normalizers For Half-Open Odd Windows

This neutral ND leaf freezes the shared value carrier used by the flat and
reciprocal A5 band profiles. Both real endpoints are rounded upward and the
upper natural endpoint is excluded. The logarithmic estimate is centered at
the successor of the inclusive natural endpoint before the real rounding is
paid; this preserves the source's vanishing `3 / (2 * z)` error.

The inherited Tao probability modules are used only through their checked
public declarations. There is no A5 schedule or Syracuse dependency here.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

/-- Positive odd natural values in the real half-open interval `[z, u)`. -/
noncomputable def oddHalfOpenRealWindow (z u : ℝ) : Finset ℕ :=
  (Finset.Ico (Nat.ceil z) (Nat.ceil u)).filter (fun N => N % 2 = 1)

theorem mem_oddHalfOpenRealWindow {z u : ℝ} {N : ℕ} :
    N ∈ oddHalfOpenRealWindow z u ↔
      z ≤ (N : ℝ) ∧ (N : ℝ) < u ∧ N % 2 = 1 := by
  simp only [oddHalfOpenRealWindow, Finset.mem_filter, Finset.mem_Ico,
    Nat.ceil_le, Nat.lt_ceil]
  tauto

/-- Bridge from the half-open carrier to an inclusive Tao odd window. -/
theorem oddHalfOpenRealWindow_eq_oddLogWindow
    {z u : ℝ} (hceil : Nat.ceil z < Nat.ceil u) :
    oddHalfOpenRealWindow z u =
      Tao.oddLogWindow (Nat.ceil z) (Nat.ceil u - 1) := by
  ext N
  simp only [oddHalfOpenRealWindow, Finset.mem_filter, Finset.mem_Ico,
    Tao.oddLogWindow_mem]
  omega

private theorem card_filter_odd_range (n : ℕ) :
    ((Finset.range n).filter (fun x => x % 2 = 1)).card = n / 2 := by
  rw [← Nat.count_eq_card_filter_range]
  have h := Nat.count_modEq_card n (by omega : 0 < 2) 1
  have hnmod : ¬ 1 < n % 2 := by
    have := Nat.mod_lt n (by omega : 0 < 2)
    omega
  simpa [Nat.ModEq, hnmod] using h

private theorem card_filter_odd_Ico {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ico a b).filter (fun x => x % 2 = 1)).card =
      b / 2 - a / 2 := by
  let p : ℕ → Prop := fun x => x % 2 = 1
  have hset :
      (Finset.Ico a b).filter p =
        (Finset.range b).filter p \ (Finset.range a).filter p := by
    ext x
    simp [p]
    omega
  have hsub :
      (Finset.range a).filter p ⊆ (Finset.range b).filter p := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨lt_of_lt_of_le hx.1 hab, hx.2⟩
  rw [hset, Finset.card_sdiff_of_subset hsub]
  simp only [p, card_filter_odd_range]

/-- Exact natural count of the shared odd carrier. -/
theorem card_oddHalfOpenRealWindow {z u : ℝ} (hzu : z ≤ u) :
    (oddHalfOpenRealWindow z u).card =
      Nat.ceil u / 2 - Nat.ceil z / 2 := by
  exact card_filter_odd_Ico (Nat.ceil_mono hzu)

private theorem ceil_half_error_bounds {t : ℝ} (ht : 0 ≤ t) :
    -(1 / 2 : ℝ) ≤ ((Nat.ceil t / 2 : ℕ) : ℝ) - t / 2 ∧
      ((Nat.ceil t / 2 : ℕ) : ℝ) - t / 2 < 1 / 2 := by
  let A := Nat.ceil t
  have htA : t ≤ (A : ℝ) := by
    simpa only [A] using Nat.le_ceil t
  have hAlt : (A : ℝ) < t + 1 := by
    simpa only [A] using Nat.ceil_lt_add_one ht
  have hmod := Nat.mod_lt A (by omega : 0 < 2)
  have hdecomp := Nat.div_add_mod A 2
  have hlowNat : A ≤ 2 * (A / 2) + 1 := by omega
  have huppNat : 2 * (A / 2) ≤ A := by omega
  have hlow : (A : ℝ) ≤ 2 * ((A / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hlowNat
  have hupp : 2 * ((A / 2 : ℕ) : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast huppNat
  constructor <;> linarith

/-- Sharp flat normalization: parity and the two ceiling defects still leave
a strict error below one. -/
theorem abs_card_oddHalfOpenRealWindow_sub_half_width_lt_one
    {z u : ℝ} (hz : 0 ≤ z) (hzu : z ≤ u) :
    |((oddHalfOpenRealWindow z u).card : ℝ) - (u - z) / 2| < 1 := by
  have hu : 0 ≤ u := hz.trans hzu
  have hcard := card_filter_odd_Ico (Nat.ceil_mono hzu)
  have hdiv : Nat.ceil z / 2 ≤ Nat.ceil u / 2 :=
    Nat.div_le_div_right (Nat.ceil_mono hzu)
  have hzErr := ceil_half_error_bounds hz
  have huErr := ceil_half_error_bounds hu
  rw [oddHalfOpenRealWindow, hcard, Nat.cast_sub hdiv, abs_lt]
  constructor <;> linarith

private noncomputable def clampedReciprocal (A N : ℕ) : ℝ :=
  1 / ((max A N : ℕ) : ℝ)

private theorem clampedReciprocal_antitone
    {A : ℕ} (hA : 1 ≤ A) : Antitone (clampedReciprocal A) := by
  intro M N hMN
  apply one_div_le_one_div_of_le
  · exact_mod_cast hA.trans (le_max_left A M)
  · exact_mod_cast max_le_max_left A hMN

private theorem clampedReciprocal_nonneg (A N : ℕ) :
    0 ≤ clampedReciprocal A N :=
  one_div_nonneg.mpr (Nat.cast_nonneg _)

private theorem clampedReciprocal_eq
    {A N : ℕ} (hAN : A ≤ N) :
    clampedReciprocal A N = 1 / (N : ℝ) := by
  simp [clampedReciprocal, max_eq_right hAN]

/-- Lower integral rectangle for an inclusive reciprocal sum, centered at the
successor of its upper endpoint. -/
theorem log_succ_div_le_sum_Icc_reciprocal
    {A U : ℕ} (hA : 1 ≤ A) (hAU : A ≤ U) :
    Real.log (((U + 1 : ℕ) : ℝ) / (A : ℝ)) ≤
      ∑ N ∈ Finset.Icc A U, 1 / (N : ℝ) := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hUonepos : (0 : ℝ) < (U + 1 : ℕ) := by positivity
  have hint :
      (∫ x : ℝ in (A : ℝ)..((U + 1 : ℕ) : ℝ), 1 / x) ≤
        ∑ N ∈ Finset.Ico A (U + 1), 1 / (N : ℝ) := by
    simpa only [one_div] using
      (@AntitoneOn.integral_le_sum_Ico A (U + 1) (fun x : ℝ => x⁻¹)
        (by omega) (inv_antitoneOn_Icc_right hApos))
  rw [Finset.Ico_add_one_right_eq_Icc] at hint
  rw [← integral_one_div_of_pos hApos hUonepos]
  exact hint

/-- Successor-centered harmonic mass of an inclusive odd window. Odd/even
interlacing and the reciprocal integral comparison each cost `1/(2A)`. -/
theorem abs_logFinsetMass_oddLogWindow_sub_half_log_succ_ratio_le
    {A U : ℕ} (hA : 1 ≤ A) (hAU : A ≤ U) :
    |Tao.logFinsetMass (Tao.oddLogWindow A U) -
        (1 / 2 : ℝ) *
          (Real.log ((U + 1 : ℕ) : ℝ) - Real.log (A : ℝ))| ≤
      1 / (A : ℝ) := by
  let w : ℕ → ℝ := clampedReciprocal A
  let rOdd : Fin 2 := ⟨1, by omega⟩
  let rEven : Fin 2 := ⟨0, by omega⟩
  let Hodd := Tao.antitoneResidueClassSum A U 2 w rOdd
  let Heven := Tao.antitoneResidueClassSum A U 2 w rEven
  let S := ∑ N ∈ Finset.Icc A U, 1 / (N : ℝ)
  let L := Real.log (((U + 1 : ℕ) : ℝ) / (A : ℝ))
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hA.trans hAU
  have hUonepos : (0 : ℝ) < (U + 1 : ℕ) := by positivity
  have hw : Antitone w := by
    simpa only [w] using clampedReciprocal_antitone hA
  have hw0 : ∀ N, 0 ≤ w N := by
    intro N
    simpa only [w] using clampedReciprocal_nonneg A N
  have hoddMass : Tao.logFinsetMass (Tao.oddLogWindow A U) = Hodd := by
    unfold Tao.logFinsetMass Hodd Tao.antitoneResidueClassSum
    apply Finset.sum_congr
    · ext N
      simp [Tao.oddLogWindow, Tao.antitoneResidueClass, rOdd]
    · intro N hN
      have hAN : A ≤ N := (Tao.oddLogWindow_mem.mp hN).1
      rw [Tao.logNatWeight_eq_one_div_of_pos (hA.trans hAN)]
      exact (clampedReciprocal_eq hAN).symm
  have hdiff : |Hodd - Heven| ≤ 1 / (A : ℝ) := by
    have h := Tao.abs_antitoneResidueClassSum_sub_le
      (A := A) (B := U) (Q := 2) (by omega) w hw hw0 rOdd rEven
    simpa [Hodd, Heven, w, clampedReciprocal] using h
  have htotal : Hodd + Heven = S := by
    have h := Tao.sum_antitoneResidueClassSum
      (A := A) (B := U) (Q := 2) (by omega) w
    have hwIcc : (∑ N ∈ Finset.Icc A U, w N) = S := by
      apply Finset.sum_congr rfl
      intro N hN
      have hAN : A ≤ N := (Finset.mem_Icc.mp hN).1
      simpa only [w] using clampedReciprocal_eq hAN
    rw [show (∑ r : Fin 2, Tao.antitoneResidueClassSum A U 2 w r) =
          Tao.antitoneResidueClassSum A U 2 w rEven +
            Tao.antitoneResidueClassSum A U 2 w rOdd by
      simp [rEven, rOdd]] at h
    dsimp [Hodd, Heven]
    rw [add_comm]
    exact h.trans hwIcc
  have hhalf : 1 / (2 * (A : ℝ)) = (1 / (A : ℝ)) / 2 := by
    field_simp
  have hoddCenter : |Hodd - S / 2| ≤ 1 / (2 * (A : ℝ)) := by
    rw [abs_le] at hdiff ⊢
    rw [hhalf]
    constructor <;> linarith
  have hSlow : L ≤ S := by
    simpa [L, S] using log_succ_div_le_sum_Icc_reciprocal hA hAU
  have hlogMono : Real.log ((U : ℝ) / (A : ℝ)) ≤ L := by
    have hratioPos : 0 < (U : ℝ) / (A : ℝ) := div_pos hUpos hApos
    have hratioOnePos : 0 < ((U + 1 : ℕ) : ℝ) / (A : ℝ) :=
      div_pos hUonepos hApos
    apply Real.strictMonoOn_log.monotoneOn hratioPos hratioOnePos
    apply div_le_div_of_nonneg_right
    · norm_num
    · exact hApos.le
  have hSup : S ≤ 1 / (A : ℝ) + L := by
    calc
      S ≤ 1 / (A : ℝ) + Real.log ((U : ℝ) / (A : ℝ)) := by
        simpa [S] using Tao.sum_Icc_reciprocal_le_one_div_add_log_div hA hAU
      _ ≤ 1 / (A : ℝ) + L := by linarith
  have hSCenter : |S / 2 - L / 2| ≤ 1 / (2 * (A : ℝ)) := by
    rw [abs_le, hhalf]
    constructor <;> linarith
  rw [hoddMass]
  have hsplit :
      Hodd - L / 2 = (Hodd - S / 2) + (S / 2 - L / 2) := by
    ring
  rw [show (1 / 2 : ℝ) *
      (Real.log ((U + 1 : ℕ) : ℝ) - Real.log (A : ℝ)) = L / 2 by
    dsimp [L]
    rw [Real.log_div hUonepos.ne' hApos.ne']
    ring]
  rw [hsplit]
  calc
    |(Hodd - S / 2) + (S / 2 - L / 2)| ≤
        |Hodd - S / 2| + |S / 2 - L / 2| := abs_add_le _ _
    _ ≤ 1 / (2 * (A : ℝ)) + 1 / (2 * (A : ℝ)) :=
      add_le_add hoddCenter hSCenter
    _ = 1 / (A : ℝ) := by rw [hhalf]; ring

private theorem log_ceil_sub_log_bounds {z t : ℝ}
    (hz : 0 < z) (hzt : z ≤ t) :
    0 ≤ Real.log (Nat.ceil t : ℝ) - Real.log t ∧
      Real.log (Nat.ceil t : ℝ) - Real.log t ≤ 1 / z := by
  have ht : 0 < t := hz.trans_le hzt
  have hceilNat : 0 < Nat.ceil t := Nat.ceil_pos.mpr ht
  have hceilPos : (0 : ℝ) < Nat.ceil t := by exact_mod_cast hceilNat
  have htCeil : t ≤ (Nat.ceil t : ℝ) := Nat.le_ceil t
  have hlogMono : Real.log t ≤ Real.log (Nat.ceil t : ℝ) :=
    Real.strictMonoOn_log.monotoneOn ht hceilPos htCeil
  have hceilLt : (Nat.ceil t : ℝ) < t + 1 :=
    Nat.ceil_lt_add_one ht.le
  have hratioPos : 0 < (Nat.ceil t : ℝ) / t := div_pos hceilPos ht
  have hlogRatio := Real.log_le_sub_one_of_pos hratioPos
  rw [Real.log_div hceilPos.ne' ht.ne'] at hlogRatio
  have hratioLt : (Nat.ceil t : ℝ) / t - 1 < 1 / t := by
    have hdiv := div_lt_div_of_pos_right hceilLt ht
    have hid : (t + 1) / t = 1 + 1 / t := by field_simp
    rw [hid] at hdiv
    linarith
  have hinv : 1 / t ≤ 1 / z := one_div_le_one_div_of_le hz hzt
  constructor
  · linarith
  · exact hlogRatio.trans (hratioLt.le.trans hinv)

/-- Sharp harmonic normalization of the real half-open odd carrier. The two
ceiling-log errors are same-signed, so their difference costs only `1/z`
before the factor `1/2`. -/
theorem abs_logFinsetMass_oddHalfOpenRealWindow_sub_half_log_width_le
    {z u : ℝ} (hz : 0 < z) (hzu : z ≤ u)
    (hceil : Nat.ceil z < Nat.ceil u) :
    |Tao.logFinsetMass (oddHalfOpenRealWindow z u) -
        (1 / 2 : ℝ) * (Real.log u - Real.log z)| ≤
      3 / (2 * z) := by
  have hAposNat : 0 < Nat.ceil z := Nat.ceil_pos.mpr hz
  have hBposNat : 0 < Nat.ceil u := hAposNat.trans hceil
  have hBsub : Nat.ceil u - 1 + 1 = Nat.ceil u :=
    Nat.sub_add_cancel hBposNat
  have hbridge := oddHalfOpenRealWindow_eq_oddLogWindow hceil
  have hSucc :=
    abs_logFinsetMass_oddLogWindow_sub_half_log_succ_ratio_le
      hAposNat (show Nat.ceil z ≤ Nat.ceil u - 1 by omega)
  have hround :
      |(Real.log (Nat.ceil u : ℝ) - Real.log (Nat.ceil z : ℝ)) -
          (Real.log u - Real.log z)| ≤ 1 / z := by
    have hzB := log_ceil_sub_log_bounds hz le_rfl
    have huB := log_ceil_sub_log_bounds hz hzu
    rw [abs_le]
    constructor <;> linarith
  have hinv : 1 / (Nat.ceil z : ℝ) ≤ 1 / z :=
    one_div_le_one_div_of_le hz (Nat.le_ceil z)
  rw [hBsub] at hSucc
  rw [hbridge]
  let H := Tao.logFinsetMass
    (Tao.oddLogWindow (Nat.ceil z) (Nat.ceil u - 1))
  let R := Real.log (Nat.ceil u : ℝ) - Real.log (Nat.ceil z : ℝ)
  let L := Real.log u - Real.log z
  have hsplit :
      H - (1 / 2 : ℝ) * L =
        (H - (1 / 2 : ℝ) * R) + (1 / 2 : ℝ) * (R - L) := by
    ring
  change |H - (1 / 2 : ℝ) * L| ≤ _
  rw [hsplit]
  calc
    |(H - (1 / 2 : ℝ) * R) + (1 / 2 : ℝ) * (R - L)| ≤
        |H - (1 / 2 : ℝ) * R| + |(1 / 2 : ℝ) * (R - L)| :=
      abs_add_le _ _
    _ ≤ 1 / (Nat.ceil z : ℝ) + (1 / 2 : ℝ) * (1 / z) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact add_le_add hSucc
        (mul_le_mul_of_nonneg_left hround (by norm_num))
    _ ≤ 1 / z + (1 / 2 : ℝ) * (1 / z) :=
      add_le_add hinv le_rfl
    _ = 3 / (2 * z) := by field_simp; ring

/-- Ceiling-independent upper bound for a possibly empty thin half-open odd
window. -/
theorem logFinsetMass_oddHalfOpenRealWindow_le_half_log_width_add_three_div
    {z u : ℝ} (hz : 0 < z) (hzu : z ≤ u) :
    Tao.logFinsetMass (oddHalfOpenRealWindow z u) ≤
      (1 / 2 : ℝ) * (Real.log u - Real.log z) + 3 / (2 * z) := by
  by_cases hceil : Nat.ceil z < Nat.ceil u
  · have hupper :=
      (abs_le.mp
        (abs_logFinsetMass_oddHalfOpenRealWindow_sub_half_log_width_le
          hz hzu hceil)).2
    linarith
  · have hceilEq : Nat.ceil z = Nat.ceil u :=
      le_antisymm (Nat.ceil_mono hzu) (not_lt.mp hceil)
    have hwindow : oddHalfOpenRealWindow z u = ∅ := by
      simp [oddHalfOpenRealWindow, hceilEq]
    have hu : 0 < u := hz.trans_le hzu
    have hlog : Real.log z ≤ Real.log u :=
      Real.strictMonoOn_log.monotoneOn hz hu hzu
    have hcenter :
        0 ≤ (1 / 2 : ℝ) * (Real.log u - Real.log z) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr hlog)
    have herr : 0 ≤ (3 : ℝ) / (2 * z) := by positivity
    simpa only [hwindow, Tao.logFinsetMass, Finset.sum_empty] using
      add_nonneg hcenter herr

end ND
end Erdos1135
