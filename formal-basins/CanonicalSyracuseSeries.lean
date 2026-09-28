import CanonicalSyracuseCylinderLaw

set_option autoImplicit false

open Filter
open scoped Topology

namespace CollatzCylinderPacking.Arithmetic

theorem padic_two_isUnit : IsUnit (2 : ℤ_[3]) := by
  by_contra h
  have hn := PadicInt.not_isUnit_iff.mp h
  have hd := (PadicInt.norm_int_lt_one_iff_dvd (p := 3) 2).mp (by simpa using hn)
  norm_num at hd

noncomputable def padicTwoUnit : ℤ_[3]ˣ := padic_two_isUnit.unit

theorem padicTwoUnit_coe : (padicTwoUnit : ℤ_[3]) = 2 := padic_two_isUnit.unit_spec

noncomputable def padicTruncatedSeries : List ℕ → ℤ_[3]
  | [] => 0
  | a :: as => ↑(padicTwoUnit⁻¹) ^ a * (1 + 3 * padicTruncatedSeries as)

theorem padic_two_unit_projection (k : ℕ) :
    Units.map (PadicInt.toZModPow k : ℤ_[3] →+* ZMod (3 ^ k)).toMonoidHom padicTwoUnit =
      powerTwoUnit k 1 := by
  apply Units.ext
  change PadicInt.toZModPow k (padicTwoUnit : ℤ_[3]) = (powerTwoUnit k 1 : ZMod (3 ^ k))
  rw [padicTwoUnit_coe, powerTwoUnit_coe, pow_one, map_ofNat]

theorem padic_inverse_projection (k : ℕ) :
    PadicInt.toZModPow k (↑(padicTwoUnit⁻¹) : ℤ_[3]) = twoInverse k := by
  change (↑(Units.map (PadicInt.toZModPow k : ℤ_[3] →+* ZMod (3 ^ k)).toMonoidHom
    (padicTwoUnit⁻¹)) : ZMod (3 ^ k)) = _
  rw [map_inv, padic_two_unit_projection]
  rfl

theorem padic_truncated_projection (k : ℕ) (as : List ℕ) :
    PadicInt.toZModPow k (padicTruncatedSeries as) = truncatedSeries k as := by
  induction as with
  | nil => simp [padicTruncatedSeries, truncatedSeries]
  | cons a as ih =>
    simp only [padicTruncatedSeries, map_mul, map_pow, map_add, map_one, map_ofNat,
      padic_inverse_projection, ih, truncatedSeries, inverse_powerTwoUnit]

theorem padic_truncated_closedForm (as : List ℕ) :
    padicTruncatedSeries as =
      ∑ j ∈ Finset.range as.length,
        (3 : ℤ_[3]) ^ j * (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (as.take (j + 1)).sum := by
  induction as with
  | nil => simp [padicTruncatedSeries]
  | cons a as ih =>
    rw [padicTruncatedSeries, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.take_succ_cons, List.sum_cons, List.take_zero, List.sum_nil,
      add_zero, pow_zero, one_mul]
    rw [mul_add, mul_one]
    have he :
        (∑ j ∈ Finset.range as.length,
          (3 : ℤ_[3]) ^ (j + 1) * (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (a + (as.take (j + 1)).sum)) =
        (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ a * (3 *
          ∑ j ∈ Finset.range as.length,
            (3 : ℤ_[3]) ^ j * (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^ (as.take (j + 1)).sum) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ, pow_add]
      ring
    rw [he]
    ring

theorem canonical_series_approximation_bound (k : ℕ) (f : ℕ → ℕ) :
    dist (padicTruncatedSeries (wordList k (sequenceWord k f)))
      (canonicalSyracuseVariable f) ≤ (1 / 3 : ℝ) ^ k := by
  have hi : canonicalSyracuseVariable f - padicTruncatedSeries (wordList k (sequenceWord k f)) ∈
      (Ideal.span {(3 : ℤ_[3]) ^ k} : Ideal ℤ_[3]) := by
    rw [← kernel_three k, RingHom.mem_ker, map_sub, canonical_variable_projection,
      padic_truncated_projection, wordResidue_eq_truncatedSeries, sub_self]
  have hn := (norm_span_three _ k).mpr hi
  rw [dist_eq_norm, norm_sub_rev]
  convert hn using 1
  simp [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- The constructed 3-adic value is the limit of the actual Syracuse series,
not only a formal compatible-residue object. -/
theorem canonical_variable_series_limit (f : ℕ → ℕ) :
    Tendsto (fun k =>
      ∑ j ∈ Finset.range k,
        (3 : ℤ_[3]) ^ j * (↑(padicTwoUnit⁻¹) : ℤ_[3]) ^
          ((wordList k (sequenceWord k f)).take (j + 1)).sum)
      atTop (𝓝 (canonicalSyracuseVariable f)) := by
  have ht : Tendsto (fun k => padicTruncatedSeries (wordList k (sequenceWord k f)))
      atTop (𝓝 (canonicalSyracuseVariable f)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun k => canonical_series_approximation_bound k f)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  simpa only [padic_truncated_closedForm, wordList_length] using ht

#print axioms padic_truncated_projection
#print axioms canonical_series_approximation_bound
#print axioms canonical_variable_series_limit

end CollatzCylinderPacking.Arithmetic
