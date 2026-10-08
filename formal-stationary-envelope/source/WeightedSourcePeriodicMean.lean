import ActualBasinPeriodicMean
import FirstHitWeightTransport

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic CollatzCanonical.GaoShortcut
open CollatzCanonical.NativeTao

theorem pathWeight_adjacent_good_difference {H q : ℕ} (hq : 0 < q)
    (hg : good H q) :
    pathWeight H (q + 1) - pathWeight H q = pathWeight H q / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1R : (0 : ℝ) < q + 1 := by positivity
  have hx : (0 : ℝ) < iterate H q := by
    exact_mod_cast CollatzCanonical.Correction.iterate_pos H hq
  have hgood := (good_iff H q).mp hg
  have h0 := hitting_path_weight (A := H) hq rfl
  have h1 := hitting_path_weight (A := H) (by omega : 0 < q + 1) rfl
  rw [← hgood.1, ← hgood.2] at h1
  have he := h0.symm.trans h1
  simp only [mul_div_assoc] at he
  have he' := mul_left_cancel₀ hx.ne' he
  simp only [Nat.cast_add, Nat.cast_one] at he'
  have hm := (div_eq_div_iff hqR.ne' hq1R.ne').mp he'
  apply (eq_div_iff hqR.ne').mpr
  nlinarith only [hm]

theorem firstHitWeight_adjacent_good_bound {H N q : ℕ}
    (hq : 2 ^ H * N < q) (hg : good H q) :
    |firstHitWeight N (q + 1) - firstHitWeight N q| ≤ 1 / (q : ℝ) := by
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have h0 := prefix_avoids_of_large H N q hq
  have h1 := prefix_avoids_of_large H N (q + 1) (by omega)
  have hgood := (good_iff H q).mp hg
  rw [firstHitWeight_prefix_factorization h1, firstHitWeight_prefix_factorization h0,
    ← hgood.1, ← sub_mul, pathWeight_adjacent_good_difference hqpos hg]
  have ha := pathWeight_bounds H q
  have hw := firstHitWeight_bounds N (iterate H q)
  rw [abs_of_nonneg (mul_nonneg (div_nonneg ha.1.le hqR.le) hw.1)]
  calc
    pathWeight H q / (q : ℝ) * firstHitWeight N (iterate H q) ≤
        pathWeight H q / (q : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hw.2
        (div_nonneg ha.1.le hqR.le)
    _ ≤ 1 / (q : ℝ) := div_le_div_of_nonneg_right ha.2 hqR.le

theorem firstHitWeight_adjacent_difference_le_one (N q : ℕ) :
    |firstHitWeight N (q + 1) - firstHitWeight N q| ≤ 1 := by
  have h0 := firstHitWeight_bounds N q
  have h1 := firstHitWeight_bounds N (q + 1)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem firstHitWeight_adjacent_variation_bound (N H X R : ℕ) (hR : 0 < R) :
    adjacentVariation (firstHitWeight N) X ≤
      (max (2 ^ H * N + 1) R : ℕ) + (X : ℝ) * (1 - goodProbability H) +
        (2 : ℝ) ^ H + (X : ℝ) / R := by
  classical
  let B := max (2 ^ H * N + 1) R
  let G := ((Finset.range X).filter (good H)).card
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hpoint (q : ℕ) :
      |firstHitWeight N (q + 1) - firstHitWeight N q| ≤
        (if q < B then (1 : ℝ) else 0) +
          (if good H q then (0 : ℝ) else 1) + 1 / R := by
    by_cases hq : q < B
    · simp only [hq, if_true]
      split_ifs <;> linarith [firstHitWeight_adjacent_difference_le_one N q,
        one_div_pos.mpr hRR]
    · have hlarge : 2 ^ H * N < q := by dsimp [B] at hq; omega
      have hRq : (R : ℝ) ≤ q := by exact_mod_cast (show R ≤ q by dsimp [B] at hq; omega)
      simp only [hq, if_false, zero_add]
      split_ifs with hg
      · simpa only [zero_add] using (firstHitWeight_adjacent_good_bound hlarge hg).trans
          (one_div_le_one_div_of_le hRR hRq)
      · linarith [firstHitWeight_adjacent_difference_le_one N q, one_div_pos.mpr hRR]
  have hsmall : (∑ q ∈ Finset.range X, if q < B then (1 : ℝ) else 0) ≤ B := by
    have hsub : (Finset.range X).filter (fun q => q < B) ⊆ Finset.range B := by
      intro q hq
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hq).2
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_range] at hc
    simpa using (show (((Finset.range X).filter (fun q => q < B)).card : ℝ) ≤ B
      by exact_mod_cast hc)
  have hbad : (∑ q ∈ Finset.range X, if good H q then (0 : ℝ) else 1) =
      (X : ℝ) - G := by
    have he (q : ℕ) : (if good H q then (0 : ℝ) else 1) =
        1 - (if good H q then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    simp [G]
  have hl : (X : ℝ) * goodProbability H - (2 : ℝ) ^ H ≤ G := good_count_lower H X
  have hsum := Finset.sum_le_sum (fun q (_ : q ∈ Finset.range X) => hpoint q)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one_div] at hsum
  rw [hbad] at hsum
  dsimp only [adjacentVariation]
  dsimp only [B] at hsmall
  nlinarith

theorem firstHitWeight_adjacentVariation (N : ℕ) :
    Tendsto (fun X => adjacentVariation (firstHitWeight N) X / (X : ℝ))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨H, hH⟩ := goodProbability_eventually (ε / 4) (by linarith)
  have hprob := hH H le_rfl
  obtain ⟨R, hR⟩ := exists_nat_gt (4 / ε)
  have hRpos : (0 : ℝ) < R := lt_trans (by positivity) hR
  have hRnat : 0 < R := by exact_mod_cast hRpos
  have hinv : 1 / (R : ℝ) < ε / 4 := by
    apply (div_lt_iff₀ hRpos).mpr
    have := (div_lt_iff₀ hε).mp hR
    nlinarith
  let C : ℝ := (max (2 ^ H * N + 1) R : ℕ) + (2 : ℝ) ^ H
  obtain ⟨X0, hX0⟩ := exists_nat_gt (2 * C / ε)
  refine ⟨max X0 1, fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX0le : (X0 : ℝ) ≤ X := by exact_mod_cast (le_trans (le_max_left _ _) hX)
  have hC : C < (ε / 2) * X := by
    have hs : 2 * C / ε < (X : ℝ) := lt_of_lt_of_le hX0 hX0le
    have hm := (div_lt_iff₀ hε).mp hs
    nlinarith
  have hsum0 : 0 ≤ adjacentVariation (firstHitWeight N) X := by
    unfold adjacentVariation
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hsum0 hXpos.le)]
  apply (div_lt_iff₀ hXpos).mpr
  have hb := firstHitWeight_adjacent_variation_bound N H X R hRnat
  have hmul := mul_le_mul_of_nonneg_left hprob hXpos.le
  have hinvmul := mul_le_mul_of_nonneg_left hinv.le hXpos.le
  rw [mul_one_div] at hinvmul
  dsimp only [C] at hC
  nlinarith

theorem firstHitWeight_abs_le_one (N q : ℕ) : |firstHitWeight N q| ≤ 1 := by
  rw [abs_of_nonneg (firstHitWeight_bounds N q).1]
  exact (firstHitWeight_bounds N q).2

theorem actual_firstHitWeight_sourceMean (N : ℕ) :
    Tendsto (sourceMean (firstHitWeight N)) atTop (𝓝 (actualFirstHitDensity N)) :=
  sourceMean_of_shift (firstHitWeight N) (firstHitWeight_abs_le_one N)
    (actual_firstHitWeight_natural_mean N)

theorem actual_firstHitWeight_periodic_sourceMean (N : ℕ) (p : ℕ → ℝ) (M : ℕ)
    (hM : 0 < M) (hp : Function.Periodic p M) :
    Tendsto (sourceMean (fun q => firstHitWeight N q * p q)) atTop
      (𝓝 (actualFirstHitDensity N * ((∑ q ∈ Finset.range M, p q) / (M : ℝ)))) :=
  periodic_weighted_mean (firstHitWeight N) p M hM hp
    (firstHitWeight_abs_le_one N) (firstHitWeight_adjacentVariation N)
    (actual_firstHitWeight_sourceMean N)

#print axioms firstHitWeight_adjacentVariation
#print axioms actual_firstHitWeight_periodic_sourceMean

def oddUnitMask (q : ℕ) : ℝ := if q % 2 = 1 ∧ q % 3 ≠ 0 then 1 else 0

theorem oddUnitMask_periodic : Function.Periodic oddUnitMask 6 := by
  intro q
  have h2 : (q + 6) % 2 = q % 2 := by omega
  have h3 : (q + 6) % 3 = q % 3 := by omega
  simp only [oddUnitMask, h2, h3]

theorem oddUnitMask_mean : (∑ q ∈ Finset.range 6, oddUnitMask q) / (6 : ℝ) = 1 / 3 := by
  have hfilter : (Finset.range 6).filter (fun q => q % 2 = 1 ∧ q % 3 ≠ 0) = {1, 5} :=
    by decide
  norm_num [oddUnitMask, hfilter]

theorem actual_firstHitWeight_oddUnit_sourceMean (N : ℕ) :
    Tendsto (sourceMean (fun q => firstHitWeight N q * oddUnitMask q)) atTop
      (𝓝 (actualFirstHitDensity N / 3)) := by
  have h := actual_firstHitWeight_periodic_sourceMean N oddUnitMask 6
    (by decide) oddUnitMask_periodic
  norm_num only [Nat.cast_ofNat] at h
  simpa only [oddUnitMask_mean, mul_one_div] using h

theorem weighted_oddUnit_abs_le_one (N q : ℕ) :
    |firstHitWeight N q * oddUnitMask q| ≤ 1 := by
  unfold oddUnitMask
  split_ifs
  · simpa only [mul_one] using firstHitWeight_abs_le_one N q
  · simp

#print axioms actual_firstHitWeight_oddUnit_sourceMean

end CollatzCanonical.PeriodicCensusFloor
