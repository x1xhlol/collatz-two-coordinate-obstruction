import Erdos1135.ND.Fourier.FiberEndpointRecurrence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A6 Signed Log Products

This leaf proves the two finite logarithmic estimates at the entrance to the
raw A6 local theorem.  It keeps the linear `d / n` error visible and stops
before Wallis normalization, exponentiation, or any tube summation.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

/-- The right-hand logarithmic increment in the exact Geom(2) endpoint ratio. -/
def ndA6RightLogTerm (n t : ℕ) : ℝ :=
  Real.log
    ((2 * (n : ℝ) + (t : ℝ)) /
      (2 * (n : ℝ) + 2 * (t : ℝ) + 2))

/-- The left-hand logarithmic increment, indexed from `t = 0`. -/
def ndA6LeftLogTerm (n t : ℕ) : ℝ :=
  Real.log
    ((2 * (n : ℝ) - 2 * (t : ℝ)) /
      (2 * (n : ℝ) - (t : ℝ) - 1))

private theorem abs_log_one_sub_add_self_le_two_mul_sq
    {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hxabs : |x| < 1 := by
    linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := x) hxabs 1
  norm_num [Finset.sum_range_succ] at h
  have hden : 0 < 1 - |x| := by linarith
  calc
    |Real.log (1 - x) + x| ≤ |x| ^ 2 / (1 - |x|) := by
      simpa [add_comm] using h
    _ ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ hden]
      rw [sq_abs]
      nlinarith [sq_nonneg x]

private theorem ndA6_rightTaylorSquares_le
    {N T D : ℝ} (hN : 0 < N) (hT : 0 ≤ T) (hTD : T + 1 ≤ D) :
    2 * (T / (2 * N)) ^ 2 + 2 * ((T + 1) / N) ^ 2 ≤
      4 * D ^ 2 / N ^ 2 := by
  have hD : 0 ≤ D := by linarith
  have htD : T ≤ D := by linarith
  have htSq : T ^ 2 ≤ D ^ 2 := (sq_le_sq₀ hT hD).2 htD
  have htpSq : (T + 1) ^ 2 ≤ D ^ 2 :=
    (sq_le_sq₀ (by linarith) hD).2 hTD
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
  calc
    2 * (T / (2 * N)) ^ 2 + 2 * ((T + 1) / N) ^ 2 =
        (T ^ 2 / 2 + 2 * (T + 1) ^ 2) / N ^ 2 := by
      field_simp
    _ ≤ (D ^ 2 / 2 + 2 * D ^ 2) / N ^ 2 := by
      exact (div_le_div_iff_of_pos_right hN2).2 (by linarith)
    _ ≤ 4 * D ^ 2 / N ^ 2 := by
      exact (div_le_div_iff_of_pos_right hN2).2 (by
        nlinarith [sq_nonneg D])

private theorem ndA6_leftTaylorSquares_le
    {N T D : ℝ} (hN : 0 < N) (hT : 0 ≤ T) (hTD : T + 1 ≤ D) :
    2 * (T / N) ^ 2 + 2 * ((T + 1) / (2 * N)) ^ 2 ≤
      4 * D ^ 2 / N ^ 2 := by
  have hD : 0 ≤ D := by linarith
  have htD : T ≤ D := by linarith
  have htSq : T ^ 2 ≤ D ^ 2 := (sq_le_sq₀ hT hD).2 htD
  have htpSq : (T + 1) ^ 2 ≤ D ^ 2 :=
    (sq_le_sq₀ (by linarith) hD).2 hTD
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
  calc
    2 * (T / N) ^ 2 + 2 * ((T + 1) / (2 * N)) ^ 2 =
        (2 * T ^ 2 + (T + 1) ^ 2 / 2) / N ^ 2 := by
      field_simp
    _ ≤ (2 * D ^ 2 + D ^ 2 / 2) / N ^ 2 := by
      exact (div_le_div_iff_of_pos_right hN2).2 (by linarith)
    _ ≤ 4 * D ^ 2 / N ^ 2 := by
      exact (div_le_div_iff_of_pos_right hN2).2 (by
        nlinarith [sq_nonneg D])

private theorem abs_ndA6RightLogRatio_add_affine_le
    {N T D : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    (hTD : T + 1 ≤ D) (hDN : 4 * D ≤ N) :
    |Real.log ((2 * N + T) / (2 * N + 2 * T + 2)) +
        (T + 2) / (2 * N)| ≤
      4 * D ^ 2 / N ^ 2 := by
  let a := T / (2 * N)
  let b := (T + 1) / N
  have hD : 0 ≤ D := by linarith
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have haHalf : a ≤ 1 / 2 := by
    dsimp [a]
    rw [div_le_iff₀ (by positivity : 0 < 2 * N)]
    nlinarith
  have hbHalf : b ≤ 1 / 2 := by
    dsimp [b]
    rw [div_le_iff₀ hN]
    nlinarith
  have hloga : |Real.log (1 + a) - a| ≤ 2 * a ^ 2 := by
    have h := abs_log_one_sub_add_self_le_two_mul_sq
      (x := -a) (by simpa [abs_of_nonneg ha0] using haHalf)
    simpa [sub_eq_add_neg] using h
  have hlogb : |Real.log (1 + b) - b| ≤ 2 * b ^ 2 := by
    have h := abs_log_one_sub_add_self_le_two_mul_sq
      (x := -b) (by simpa [abs_of_nonneg hb0] using hbHalf)
    simpa [sub_eq_add_neg] using h
  have hfactor :
      (2 * N + T) / (2 * N + 2 * T + 2) = (1 + a) / (1 + b) := by
    dsimp [a, b]
    (field_simp [ne_of_gt hN]; ring)
  have hlogeq :
      Real.log ((2 * N + T) / (2 * N + 2 * T + 2)) =
        Real.log (1 + a) - Real.log (1 + b) := by
    rw [hfactor, Real.log_div (by positivity) (by positivity)]
  calc
    |Real.log ((2 * N + T) / (2 * N + 2 * T + 2)) +
        (T + 2) / (2 * N)| =
        |(Real.log (1 + a) - a) - (Real.log (1 + b) - b)| := by
      rw [hlogeq]
      congr 1
      dsimp [a, b]
      (field_simp [ne_of_gt hN]; ring)
    _ ≤ |Real.log (1 + a) - a| + |-(Real.log (1 + b) - b)| := by
      simpa [sub_eq_add_neg] using
        abs_add_le (Real.log (1 + a) - a) (-(Real.log (1 + b) - b))
    _ = |Real.log (1 + a) - a| + |Real.log (1 + b) - b| := by
      rw [abs_neg]
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := add_le_add hloga hlogb
    _ ≤ 4 * D ^ 2 / N ^ 2 := by
      exact ndA6_rightTaylorSquares_le hN hT hTD

private theorem abs_ndA6LeftLogRatio_add_affine_le
    {N T D : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    (hTD : T + 1 ≤ D) (hDN : 4 * D ≤ N) :
    |Real.log ((2 * N - 2 * T) / (2 * N - T - 1)) +
        (T - 1) / (2 * N)| ≤
      4 * D ^ 2 / N ^ 2 := by
  let a := T / N
  let b := (T + 1) / (2 * N)
  have hD : 0 ≤ D := by linarith
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have haHalf : a ≤ 1 / 2 := by
    dsimp [a]
    rw [div_le_iff₀ hN]
    nlinarith
  have hbHalf : b ≤ 1 / 2 := by
    dsimp [b]
    rw [div_le_iff₀ (by positivity : 0 < 2 * N)]
    nlinarith
  have hloga : |Real.log (1 - a) + a| ≤ 2 * a ^ 2 :=
    abs_log_one_sub_add_self_le_two_mul_sq
      (by simpa [abs_of_nonneg ha0] using haHalf)
  have hlogb : |Real.log (1 - b) + b| ≤ 2 * b ^ 2 :=
    abs_log_one_sub_add_self_le_two_mul_sq
      (by simpa [abs_of_nonneg hb0] using hbHalf)
  have hfactor :
      (2 * N - 2 * T) / (2 * N - T - 1) = (1 - a) / (1 - b) := by
    dsimp [a, b]
    (field_simp [ne_of_gt hN]; ring)
  have hlogeq :
      Real.log ((2 * N - 2 * T) / (2 * N - T - 1)) =
        Real.log (1 - a) - Real.log (1 - b) := by
    rw [hfactor, Real.log_div (by linarith) (by linarith)]
  calc
    |Real.log ((2 * N - 2 * T) / (2 * N - T - 1)) +
        (T - 1) / (2 * N)| =
        |(Real.log (1 - a) + a) - (Real.log (1 - b) + b)| := by
      rw [hlogeq]
      congr 1
      dsimp [a, b]
      (field_simp [ne_of_gt hN]; ring)
    _ ≤ |Real.log (1 - a) + a| + |-(Real.log (1 - b) + b)| := by
      simpa [sub_eq_add_neg] using
        abs_add_le (Real.log (1 - a) + a) (-(Real.log (1 - b) + b))
    _ = |Real.log (1 - a) + a| + |Real.log (1 - b) + b| := by
      rw [abs_neg]
    _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := add_le_add hloga hlogb
    _ ≤ 4 * D ^ 2 / N ^ 2 := by
      exact ndA6_leftTaylorSquares_le hN hT hTD

private theorem sum_range_ndA6RightAffine
    {N : ℝ} (hN : N ≠ 0) (d : ℕ) :
    (∑ t ∈ Finset.range d, ((t : ℝ) + 2) / (2 * N)) =
      ((d : ℝ) ^ 2 + 3 * (d : ℝ)) / (4 * N) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp [hN]
      ring

private theorem sum_range_ndA6LeftAffine
    {N : ℝ} (hN : N ≠ 0) (d : ℕ) :
    (∑ t ∈ Finset.range d, ((t : ℝ) - 1) / (2 * N)) =
      ((d : ℝ) ^ 2 - 3 * (d : ℝ)) / (4 * N) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp [hN]
      ring

private theorem ndGeom2_rightLogProduct_skew_cubic
    {n d : ℕ} (hn : 0 < n) (hd : 4 * d ≤ n) :
    |(∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
        ((d : ℝ) ^ 2 + 3 * (d : ℝ)) / (4 * (n : ℝ))| ≤
      4 * (d : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
  let N := (n : ℝ)
  let D := (d : ℝ)
  have hN : 0 < N := by
    simpa [N] using (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
  have hDN : 4 * D ≤ N := by
    simpa [N, D] using (show (4 : ℝ) * (d : ℝ) ≤ (n : ℝ) by
      exact_mod_cast hd)
  have hmain := sum_range_ndA6RightAffine (N := N) hN.ne' d
  change
    |(∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
        (D ^ 2 + 3 * D) / (4 * N)| ≤ 4 * D ^ 3 / N ^ 2
  rw [← hmain, ← Finset.sum_add_distrib]
  calc
    |(∑ t ∈ Finset.range d,
        (ndA6RightLogTerm n t + ((t : ℝ) + 2) / (2 * N)))| ≤
        ∑ t ∈ Finset.range d,
          |ndA6RightLogTerm n t + ((t : ℝ) + 2) / (2 * N)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range d, 4 * D ^ 2 / N ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      have htd : t < d := Finset.mem_range.mp ht
      have htD : (t : ℝ) + 1 ≤ D := by
        have htd' : t + 1 ≤ d := Nat.succ_le_iff.mpr htd
        simpa [D] using (show ((t + 1 : ℕ) : ℝ) ≤ (d : ℝ) by
          exact_mod_cast htd')
      simpa [ndA6RightLogTerm, N, D] using
        abs_ndA6RightLogRatio_add_affine_le hN
          (show 0 ≤ (t : ℝ) by positivity) htD hDN
    _ = 4 * D ^ 3 / N ^ 2 := by
      simp [D]
      ring

private theorem ndGeom2_leftLogProduct_skew_cubic
    {n d : ℕ} (hn : 0 < n) (hd : 4 * d ≤ n) :
    |(∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
        ((d : ℝ) ^ 2 - 3 * (d : ℝ)) / (4 * (n : ℝ))| ≤
      4 * (d : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
  let N := (n : ℝ)
  let D := (d : ℝ)
  have hN : 0 < N := by
    simpa [N] using (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
  have hDN : 4 * D ≤ N := by
    simpa [N, D] using (show (4 : ℝ) * (d : ℝ) ≤ (n : ℝ) by
      exact_mod_cast hd)
  have hmain := sum_range_ndA6LeftAffine (N := N) hN.ne' d
  change
    |(∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
        (D ^ 2 - 3 * D) / (4 * N)| ≤ 4 * D ^ 3 / N ^ 2
  rw [← hmain, ← Finset.sum_add_distrib]
  calc
    |(∑ t ∈ Finset.range d,
        (ndA6LeftLogTerm n t + ((t : ℝ) - 1) / (2 * N)))| ≤
        ∑ t ∈ Finset.range d,
          |ndA6LeftLogTerm n t + ((t : ℝ) - 1) / (2 * N)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ Finset.range d, 4 * D ^ 2 / N ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      have htd : t < d := Finset.mem_range.mp ht
      have htD : (t : ℝ) + 1 ≤ D := by
        have htd' : t + 1 ≤ d := Nat.succ_le_iff.mpr htd
        simpa [D] using (show ((t + 1 : ℕ) : ℝ) ≤ (d : ℝ) by
          exact_mod_cast htd')
      simpa [ndA6LeftLogTerm, N, D] using
        abs_ndA6LeftLogRatio_add_affine_le hN
          (show 0 ≤ (t : ℝ) by positivity) htD hDN
    _ = 4 * D ^ 3 / N ^ 2 := by
      simp [D]
      ring

/-- The right signed logarithmic product has its Gaussian quadratic main term.
The separate `d / n` term retains the exact negative-binomial skew. -/
theorem ndGeom2_rightLogProduct_cubic
    {n d : ℕ} (hn : 0 < n) (hd : 4 * d ≤ n) :
    |(∑ t ∈ Finset.range d,
        Real.log
          ((2 * (n : ℝ) + (t : ℝ)) /
            (2 * (n : ℝ) + 2 * (t : ℝ) + 2))) +
        (d : ℝ) ^ 2 / (4 * (n : ℝ))| ≤
      16 * ((d : ℝ) / (n : ℝ) +
        (d : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
  let N := (n : ℝ)
  let D := (d : ℝ)
  have hN : 0 < N := by
    simpa [N] using (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
  have hD : 0 ≤ D := by positivity
  have hstrong := ndGeom2_rightLogProduct_skew_cubic hn hd
  change
    |(∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
        D ^ 2 / (4 * N)| ≤ 16 * (D / N + D ^ 3 / N ^ 2)
  have hskew : 0 ≤ 3 * D / (4 * N) := by positivity
  calc
    |(∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
        D ^ 2 / (4 * N)| =
        |((∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
            (D ^ 2 + 3 * D) / (4 * N)) +
          -(3 * D / (4 * N))| := by
      congr 1
      field_simp [ne_of_gt hN]
      ring
    _ ≤
        |(∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
            (D ^ 2 + 3 * D) / (4 * N)| +
          |-(3 * D / (4 * N))| := abs_add_le _ _
    _ =
        |(∑ t ∈ Finset.range d, ndA6RightLogTerm n t) +
            (D ^ 2 + 3 * D) / (4 * N)| +
          3 * D / (4 * N) := by rw [abs_neg, abs_of_nonneg hskew]
    _ ≤ 4 * D ^ 3 / N ^ 2 + 3 * D / (4 * N) := by
      simpa [N, D] using add_le_add_right hstrong (3 * D / (4 * N))
    _ ≤ 16 * (D / N + D ^ 3 / N ^ 2) := by
      have hu : 0 ≤ D / N := div_nonneg hD hN.le
      have hv : 0 ≤ D ^ 3 / N ^ 2 := by positivity
      rw [show 4 * D ^ 3 / N ^ 2 = 4 * (D ^ 3 / N ^ 2) by ring]
      rw [show 3 * D / (4 * N) = (3 / 4 : ℝ) * (D / N) by ring]
      nlinarith

/-- The left signed logarithmic product, with the source's `u = t + 1`
indexing, has the same public quadratic bound. -/
theorem ndGeom2_leftLogProduct_cubic
    {n d : ℕ} (hn : 0 < n) (hd : 4 * d ≤ n) :
    |(∑ t ∈ Finset.range d,
        Real.log
          ((2 * (n : ℝ) - 2 * (t : ℝ)) /
            (2 * (n : ℝ) - (t : ℝ) - 1))) +
        (d : ℝ) ^ 2 / (4 * (n : ℝ))| ≤
      16 * ((d : ℝ) / (n : ℝ) +
        (d : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
  let N := (n : ℝ)
  let D := (d : ℝ)
  have hN : 0 < N := by
    simpa [N] using (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
  have hD : 0 ≤ D := by positivity
  have hstrong := ndGeom2_leftLogProduct_skew_cubic hn hd
  change
    |(∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
        D ^ 2 / (4 * N)| ≤ 16 * (D / N + D ^ 3 / N ^ 2)
  have hskew : 0 ≤ 3 * D / (4 * N) := by positivity
  calc
    |(∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
        D ^ 2 / (4 * N)| =
        |((∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
            (D ^ 2 - 3 * D) / (4 * N)) +
          3 * D / (4 * N)| := by
      congr 1
      field_simp [ne_of_gt hN]
      ring
    _ ≤
        |(∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
            (D ^ 2 - 3 * D) / (4 * N)| +
          |3 * D / (4 * N)| := abs_add_le _ _
    _ =
        |(∑ t ∈ Finset.range d, ndA6LeftLogTerm n t) +
            (D ^ 2 - 3 * D) / (4 * N)| +
          3 * D / (4 * N) := by rw [abs_of_nonneg hskew]
    _ ≤ 4 * D ^ 3 / N ^ 2 + 3 * D / (4 * N) := by
      simpa [N, D] using add_le_add_right hstrong (3 * D / (4 * N))
    _ ≤ 16 * (D / N + D ^ 3 / N ^ 2) := by
      have hu : 0 ≤ D / N := div_nonneg hD hN.le
      have hv : 0 ≤ D ^ 3 / N ^ 2 := by positivity
      rw [show 4 * D ^ 3 / N ^ 2 = 4 * (D ^ 3 / N ^ 2) by ring]
      rw [show 3 * D / (4 * N) = (3 / 4 : ℝ) * (D / N) by ring]
      nlinarith

end

end ND
end Erdos1135
