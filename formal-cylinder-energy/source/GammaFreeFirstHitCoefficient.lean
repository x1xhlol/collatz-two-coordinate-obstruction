import SyracuseFirstHitGeometry
import SyracuseUnitNonperiodicFan
import ExactFirstHitCoefficient

set_option autoImplicit false
open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao Erdos1135

noncomputable section

theorem finite_syracuse_fan_geometric_bound (Q : Finset ℕ) (y : ℕ)
    (hodd : ∀ q ∈ Q, Odd q) (hnext : ∀ q ∈ Q, Tao.syracuse q = y) :
    (∑ q ∈ Q, (1 / 2 : ℝ) ^ Tao.syracuseExponent q) ≤ 1 := by
  let E := Q.image Tao.syracuseExponent
  have hzero : 0 ∉ E := by
    rintro h
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp h
    have := Tao.syracuseExponent_pos_of_odd (hodd q hq)
    omega
  have hgeom := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).sum_le_tsum (insert 0 E)
      (fun a _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) a)
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1), Finset.sum_insert hzero] at hgeom
  have hsum : (∑ a ∈ E, (1 / 2 : ℝ) ^ a) =
      ∑ q ∈ Q, (1 / 2 : ℝ) ^ Tao.syracuseExponent q := by
    apply Finset.sum_image
    intro q hq r hr he
    exact syracuse_predecessor_exponent_injective y (hnext q hq) (hnext r hr) he
  rw [hsum] at hgeom
  norm_num at hgeom
  linarith

theorem finite_firstHit_fan_bound (Q : Finset ℕ) {N y k : ℕ}
    (hN : Odd N) (hodd : ∀ q ∈ Q, Odd q)
    (hnext : ∀ q ∈ Q, Tao.syracuse q = y)
    (hfirst : ∀ q ∈ Q, SyrFirstHit q N (k + 1)) :
    (∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / q) ≤
      3 * ((N : ℝ) * firstHitWeight N y / y) := by
  have hnonneg : 0 ≤ (N : ℝ) * firstHitWeight N y / y :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg N) (firstHitWeight_bounds N y).1)
      (Nat.cast_nonneg y)
  calc
    (∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / q) =
        ∑ q ∈ Q, (3 * (1 / 2 : ℝ) ^ Tao.syracuseExponent q) *
          ((N : ℝ) * firstHitWeight N y / y) := by
      apply Finset.sum_congr rfl
      intro q hq
      simpa only [hnext q hq] using
        syrFirstHit_coefficient_succ (hodd q hq) hN (hfirst q hq)
    _ = (3 * ((N : ℝ) * firstHitWeight N y / y)) *
        (∑ q ∈ Q, (1 / 2 : ℝ) ^ Tao.syracuseExponent q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ (3 * ((N : ℝ) * firstHitWeight N y / y)) * 1 :=
      mul_le_mul_of_nonneg_left (finite_syracuse_fan_geometric_bound Q y hodd hnext)
        (by positivity)
    _ = _ := mul_one _

theorem short_predecessor_coefficient_bound {q y N k : ℕ}
    (hq : Odd q) (hN : Odd N) (hnext : Tao.syracuse q = y)
    (hexp : Tao.syracuseExponent q ≤ 6) (hf : SyrFirstHit q N (k + 1)) :
    3 * ((N : ℝ) * firstHitWeight N y / y) ≤
      64 * ((N : ℝ) * firstHitWeight N q / q) := by
  have hcoef := syrFirstHit_coefficient_succ hq hN hf
  rw [hnext] at hcoef
  have hpow : (1 / 64 : ℝ) ≤ (1 / 2 : ℝ) ^ Tao.syracuseExponent q := by
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hexp
    norm_num at h
    exact h
  have hnonneg : 0 ≤ (N : ℝ) * firstHitWeight N y / y :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg N) (firstHitWeight_bounds N y).1)
      (Nat.cast_nonneg y)
  rw [hcoef]
  nlinarith

/-- Every finite collection of positive odd-depth first-hit leaves is controlled
by a unit nonperiodic cut at the same depth. No cycle-return factor occurs. -/
theorem finite_odd_firstHit_coefficient_bound {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ q : ℕ, 0 < q → q % 3 ≠ 0 → b / (q : ℝ) ≤ actualFirstHitDensity q)
    (Q : Finset ℕ) {N k : ℕ} (hN : Odd N)
    (hodd : ∀ q ∈ Q, Odd q) (hfirst : ∀ q ∈ Q, SyrFirstHit q N (k + 1)) :
    (∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / q) ≤
      64 * ((N : ℝ) * actualFirstHitDensity N / b) := by
  let Y := Q.image Tao.syracuse
  have hselect : ∀ y : ℕ, ∃ q : ℕ, y ∈ Y →
      Odd q ∧ q % 3 ≠ 0 ∧ Tao.syracuse q = y ∧
        Tao.syracuseExponent q ≤ 6 ∧
        (¬ ∃ r : ℕ, 0 < r ∧ iterate r q = q) ∧ SyrFirstHit q N (k + 1) := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨r, hr, hry⟩ := Finset.mem_image.mp hy
      have hyodd : Odd y := hry ▸ Tao.syracuse_odd r
      have hyunit : y % 3 ≠ 0 := hry ▸ syracuse_not_dvd_three r
      obtain ⟨q, _, hqodd, hqunit, hqy, hqa, hqnp⟩ :=
        exists_short_unit_nonperiodic_syracuse_predecessor hyodd hyunit
      have hyfirst : SyrFirstHit y N k := by
        simpa only [hry] using ((syrFirstHit_succ_iff r N k).mp (hfirst r hr)).2
      exact ⟨q, fun _ => ⟨hqodd, hqunit, hqy, hqa, hqnp,
        syrFirstHit_prepend_nonperiodic hqodd hqy hyfirst hqnp⟩⟩
    · exact ⟨0, fun h => (hy h).elim⟩
  choose select hsel using hselect
  let P := Y.image select
  have hinj : ∀ y ∈ Y, ∀ z ∈ Y, select y = select z → y = z := by
    intro y hy z hz he
    exact (hsel y hy).2.2.1.symm.trans
      ((congrArg Tao.syracuse he).trans (hsel z hz).2.2.1)
  have hpodd : ∀ q ∈ P, q % 2 = 1 := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.odd_iff.mp (hsel y hy).1
  have hpunit : ∀ q ∈ P, q % 3 ≠ 0 := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    exact (hsel y hy).2.1
  have hpfirst : ∀ q ∈ P, SyrFirstHit q N (k + 1) := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    exact (hsel y hy).2.2.2.2.2
  have hpnp : ∀ q ∈ P, ¬ ∃ r : ℕ, 0 < r ∧ iterate r q = q := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    exact (hsel y hy).2.2.2.2.1
  let time (q : ℕ) : ℕ := if hq : Odd q then
    Tao.taoTupleWeight (Tao.syracuseValuationPNatList (k + 1) q hq) else 0
  have htime (q : ℕ) (hq : q ∈ P) : FirstHit q N (time q) ∧ oddCount (time q) q = k + 1 := by
    have ho := Nat.odd_iff.mpr (hpodd q hq)
    dsimp only [time]
    rw [dif_pos ho]
    exact ⟨(syrFirstHit_iff_shortcut_firstHit ho hN).mp (hpfirst q hq),
      syracuse_shortcut_oddCount (k + 1) q ho⟩
  have hcut := finite_unit_nonperiodic_firstHit_coefficient_bound hb hfloor P N (k + 1)
    time hpodd hpunit (fun q hq => (htime q hq).1) (fun q hq => (htime q hq).2) hpnp
  have hsplit := Finset.sum_fiberwise_of_maps_to
    (fun q (hq : q ∈ Q) => Finset.mem_image_of_mem Tao.syracuse hq)
    (fun q => (N : ℝ) * firstHitWeight N q / q)
  calc
    (∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / q) =
        ∑ y ∈ Y, ∑ q ∈ Q with Tao.syracuse q = y,
          (N : ℝ) * firstHitWeight N q / q := hsplit.symm
    _ ≤ ∑ y ∈ Y, 64 * ((N : ℝ) * firstHitWeight N (select y) / select y) := by
      apply Finset.sum_le_sum
      intro y hy
      apply le_trans (finite_firstHit_fan_bound (Q.filter (fun q => Tao.syracuse q = y)) hN
        (fun q hq => hodd q (Finset.mem_filter.mp hq).1)
        (fun q hq => (Finset.mem_filter.mp hq).2)
        (fun q hq => hfirst q (Finset.mem_filter.mp hq).1))
      exact short_predecessor_coefficient_bound (hsel y hy).1 hN
        (hsel y hy).2.2.1 (hsel y hy).2.2.2.1 (hsel y hy).2.2.2.2.2
    _ = 64 * (∑ q ∈ P, (N : ℝ) * firstHitWeight N q / q) := by
      rw [← Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ 64 * ((N : ℝ) * actualFirstHitDensity N / b) :=
      mul_le_mul_of_nonneg_left hcut (by norm_num)

theorem exactFirstHitCoefficient_le_density {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ q : ℕ, 0 < q → q % 3 ≠ 0 → b / (q : ℝ) ≤ actualFirstHitDensity q)
    {N : ℕ} (hN : Odd N) (k : ℕ) :
    exactFirstHitCoefficient (k + 1) N ≤
      64 * ((N : ℝ) * actualFirstHitDensity N / b) := by
  unfold exactFirstHitCoefficient
  apply (exactFirstHitTerm_summable hN.pos (k + 1)).tsum_le_of_sum_le
  intro Q
  let P := Q.filter (fun q => q % 2 = 1 ∧
    ∃ A, FirstHit q N A ∧ oddCount A q = k + 1)
  have hpodd : ∀ q ∈ P, Odd q := by
    intro q hq
    exact Nat.odd_iff.mpr (Finset.mem_filter.mp hq).2.1
  have hpfirst : ∀ q ∈ P, SyrFirstHit q N (k + 1) := by
    intro q hq
    exact (shortcut_firstHit_odd_depth_iff_syrFirstHit (hpodd q hq) hN).mp
      (Finset.mem_filter.mp hq).2.2
  have h := finite_odd_firstHit_coefficient_bound hb hfloor P hN hpodd hpfirst
  simpa only [P, Finset.sum_filter, exactFirstHitTerm] using h

theorem canonicalRho_le_density_of_finite_no_return {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ q : ℕ, 0 < q → q % 3 ≠ 0 → b / (q : ℝ) ≤ actualFirstHitDensity q)
    {N : ℕ} (hN : Odd N) (k : ℕ)
    (hno : ∀ j : ℕ, 0 < j → j ≤ k + 1 → (Tao.syracuse^[j]) N ≠ N) :
    canonicalRho (k + 1) N ≤ 64 * ((N : ℝ) * actualFirstHitDensity N / b) := by
  rw [canonicalRho_eq_exactFirstHitCoefficient_of_finite_no_return hN k hno]
  exact exactFirstHitCoefficient_le_density hb hfloor hN k

/-- A universal bound at each positive exact first-hit depth, including periodic targets. -/
theorem exists_uniform_odd_exact_firstHit_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Odd N → ∀ k : ℕ, 0 < k →
      exactFirstHitCoefficient k N ≤ C * (N : ℝ) * actualFirstHitDensity N := by
  obtain ⟨b, hb, hfloor⟩ := exists_uniform_firstHit_reciprocal_floor
  refine ⟨64 / b, by positivity, ?_⟩
  intro N hN k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  convert exactFirstHitCoefficient_le_density hb hfloor hN j using 1
  ring

/-- The finite no-return mask transfers the same bound to actual cylinder density. -/
theorem exists_uniform_odd_masked_cylinder_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Odd N → ∀ k : ℕ, 0 < k →
      (∀ j : ℕ, 0 < j → j ≤ k → (Tao.syracuse^[j]) N ≠ N) →
      canonicalRho k N ≤ C * (N : ℝ) * actualFirstHitDensity N := by
  obtain ⟨b, hb, hfloor⟩ := exists_uniform_firstHit_reciprocal_floor
  refine ⟨64 / b, by positivity, ?_⟩
  intro N hN k hk hno
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  convert canonicalRho_le_density_of_finite_no_return hb hfloor hN j hno using 1
  ring

#print axioms finite_odd_firstHit_coefficient_bound
#print axioms exactFirstHitCoefficient_le_density
#print axioms exists_uniform_odd_exact_firstHit_coefficient_bound
#print axioms exists_uniform_odd_masked_cylinder_bound
end
end CollatzCanonical.PeriodicCensusFloor
