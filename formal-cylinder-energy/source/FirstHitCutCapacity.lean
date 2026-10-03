import CanonicalTracePolynomialFloor
import FirstHitWeightTransport
import ShortcutOddEndpoints
import NativeSyracuseClockBridge

set_option autoImplicit false
open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.DirichletAbelian CollatzCanonical.NativeTao Erdos1135

noncomputable section

theorem prefix_avoids_target_of_nonperiodic_landing {x q N A : ℕ}
    (hland : iterate A x = q) (hqN : ∃ B, iterate B q = N)
    (hqnp : ¬ ∃ r : ℕ, 0 < r ∧ iterate r q = q) :
    ∀ i < A, iterate i x ≠ N := by
  intro i hi he
  obtain ⟨B, hB⟩ := hqN
  have hback : iterate (A - i) N = q := by
    rw [← he, ← iterate_add, Nat.add_sub_of_le hi.le, hland]
  apply hqnp
  refine ⟨B + (A - i), by omega, ?_⟩
  rw [iterate_add, hB, hback]

theorem nonperiodic_leaf_weight_factorization {q N x : ℕ}
    (hqN : ∃ A, iterate A q = N)
    (hqnp : ¬ ∃ r : ℕ, 0 < r ∧ iterate r q = q)
    (hxq : ∃ A, iterate A x = q) :
    firstHitWeight N x = firstHitWeight N q * firstHitWeight q x := by
  have hf := firstHit_find hxq
  have havoid := prefix_avoids_target_of_nonperiodic_landing hf.1 hqN hqnp
  rw [firstHitWeight_prefix_factorization havoid, hf.1,
    firstHitWeight_eq_pathWeight hf]
  ring

/-- Equal first-hit odd depth makes nonperiodic odd leaves a cut of full basins. -/
theorem equal_depth_nonperiodic_leaves_disjoint {q r N x A B k : ℕ}
    (hqodd : q % 2 = 1) (hrodd : r % 2 = 1)
    (hqfirst : FirstHit q N A) (hrfirst : FirstHit r N B)
    (hqdepth : oddCount A q = k) (hrdepth : oddCount B r = k)
    (hqnp : ¬ ∃ t : ℕ, 0 < t ∧ iterate t q = q)
    (hrnp : ¬ ∃ t : ℕ, 0 < t ∧ iterate t r = r)
    (hxq : ∃ t, iterate t x = q) (hxr : ∃ t, iterate t x = r) : q = r := by
  have hforward (a b A B : ℕ) (haodd : a % 2 = 1)
      (haf : FirstHit a N A) (hbf : FirstHit b N B)
      (hda : oddCount A a = k) (hdb : oddCount B b = k)
      (hbnp : ¬ ∃ t : ℕ, 0 < t ∧ iterate t b = b)
      (hab : ∃ t, iterate t a = b) : a = b := by
    obtain ⟨t, ht⟩ := hab
    have havoid := prefix_avoids_target_of_nonperiodic_landing ht ⟨B, hbf.1⟩ hbnp
    have hbf' : FirstHit (iterate t a) N B := by simpa only [ht] using hbf
    have htime := firstHit_time_unique haf (firstHit_prepend havoid hbf')
    have hcount := congrArg (fun j => oddCount j a) htime
    dsimp only at hcount
    rw [hda, oddCount_add, ht, hdb] at hcount
    have hzero : t = 0 := by
      by_contra hne
      have hp := oddCount_pos_of_odd_start (Nat.pos_of_ne_zero hne) haodd
      omega
    simpa only [hzero, iterate] using ht
  obtain ⟨s, hs⟩ := hxq
  obtain ⟨t, ht⟩ := hxr
  rcases le_total s t with hst | hts
  · apply hforward q r A B hqodd hqfirst hrfirst hqdepth hrdepth hrnp
    refine ⟨t - s, ?_⟩
    rw [← hs, ← iterate_add, Nat.add_sub_of_le hst, ht]
  · symm
    apply hforward r q B A hrodd hrfirst hqfirst hrdepth hqdepth hqnp
    refine ⟨s - t, ?_⟩
    rw [← ht, ← iterate_add, Nat.add_sub_of_le hts, hs]

/-- A finite disjoint family of full first-hit basins carries at most the target weight. -/
theorem firstHit_cut_pointwise (Q : Finset ℕ) (N : ℕ)
    (hreach : ∀ q ∈ Q, ∃ A, iterate A q = N)
    (hnp : ∀ q ∈ Q, ¬ ∃ r : ℕ, 0 < r ∧ iterate r q = q)
    (hdisjoint : ∀ q ∈ Q, ∀ r ∈ Q, ∀ x : ℕ,
      (∃ A, iterate A x = q) → (∃ A, iterate A x = r) → q = r) (x : ℕ) :
    (∑ q ∈ Q, firstHitWeight N q * firstHitWeight q x) ≤ firstHitWeight N x := by
  by_cases hx : ∃ q ∈ Q, ∃ A, iterate A x = q
  · obtain ⟨q, hq, hxq⟩ := hx
    rw [Finset.sum_eq_single q]
    · exact (nonperiodic_leaf_weight_factorization (hreach q hq) (hnp q hq) hxq).symm.le
    · intro r hr hrq
      have hno : ¬ ∃ A, iterate A x = r := by
        intro hxr
        exact hrq (hdisjoint r hr q hq x hxr hxq)
      simp [firstHitWeight, hno]
    · exact fun h => (h hq).elim
  · have hz : ∀ q ∈ Q, firstHitWeight q x = 0 := by
      intro q hq
      have hno : ¬ ∃ A, iterate A x = q := fun h => hx ⟨q, hq, h⟩
      simp [firstHitWeight, hno]
    have hsum : (∑ q ∈ Q, firstHitWeight N q * firstHitWeight q x) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      rw [hz q hq, mul_zero]
    rw [hsum]
    exact (firstHitWeight_bounds N x).1

theorem logarithmicCumulative_finset_sum (Q : Finset ℕ) (w : ℕ → ℕ → ℝ) (t : ℝ) :
    logarithmicCumulative (fun x => ∑ q ∈ Q, w q x) t =
      ∑ q ∈ Q, logarithmicCumulative (w q) t := by
  unfold logarithmicCumulative
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]

/-- Only finite linearity of actual weighted logarithmic means is needed. -/
theorem firstHit_cut_density (Q : Finset ℕ) (N : ℕ)
    (hpoint : ∀ x : ℕ,
      (∑ q ∈ Q, firstHitWeight N q * firstHitWeight q x) ≤ firstHitWeight N x) :
    (∑ q ∈ Q, firstHitWeight N q * actualFirstHitDensity q) ≤ actualFirstHitDensity N := by
  have hl := tendsto_finset_sum Q (fun q _ =>
    (actual_firstHitWeight_full_mean q).const_mul (firstHitWeight N q))
  apply le_of_tendsto_of_tendsto hl (actual_firstHitWeight_full_mean N)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h := logarithmicCumulative_le_of_positive_weights (fun x _ => hpoint x) t
  rw [logarithmicCumulative_finset_sum] at h
  simp_rw [logarithmicCumulative_const_mul] at h
  have hd := div_le_div_of_nonneg_right h ht
  simpa only [Finset.sum_div, mul_div_assoc] using hd

/-- A unit first-hit cut converts the native reciprocal density floor into a coefficient bound. -/
theorem firstHit_cut_coefficient_bound {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ q : ℕ, 0 < q → q % 3 ≠ 0 → b / (q : ℝ) ≤ actualFirstHitDensity q)
    (Q : Finset ℕ) (N : ℕ)
    (hqpos : ∀ q ∈ Q, 0 < q) (hunit : ∀ q ∈ Q, q % 3 ≠ 0)
    (hpoint : ∀ x : ℕ,
      (∑ q ∈ Q, firstHitWeight N q * firstHitWeight q x) ≤ firstHitWeight N x) :
    (∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / (q : ℝ)) ≤
      (N : ℝ) * actualFirstHitDensity N / b := by
  have h := firstHit_cut_density Q N hpoint
  have hlow : b * (∑ q ∈ Q, firstHitWeight N q / (q : ℝ)) ≤ actualFirstHitDensity N := by
    apply le_trans _ h
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hf := mul_le_mul_of_nonneg_left (hfloor q (hqpos q hq) (hunit q hq))
      (firstHitWeight_bounds N q).1
    convert hf using 1
    ring
  have hdiv := (le_div_iff₀ hb).mpr (by simpa only [mul_comm] using hlow)
  have hm := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg N)
  simpa only [Finset.mul_sum, mul_div_assoc] using hm

theorem finite_unit_nonperiodic_firstHit_coefficient_bound {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ q : ℕ, 0 < q → q % 3 ≠ 0 → b / (q : ℝ) ≤ actualFirstHitDensity q)
    (Q : Finset ℕ) (N k : ℕ) (time : ℕ → ℕ)
    (hodd : ∀ q ∈ Q, q % 2 = 1) (hunit : ∀ q ∈ Q, q % 3 ≠ 0)
    (hfirst : ∀ q ∈ Q, FirstHit q N (time q))
    (hdepth : ∀ q ∈ Q, oddCount (time q) q = k)
    (hnp : ∀ q ∈ Q, ¬ ∃ r : ℕ, 0 < r ∧ iterate r q = q) :
    (∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / (q : ℝ)) ≤
      (N : ℝ) * actualFirstHitDensity N / b := by
  apply firstHit_cut_coefficient_bound hb hfloor Q N
    (fun q hq => by have := hodd q hq; omega) hunit
  apply firstHit_cut_pointwise Q N (fun q hq => ⟨time q, (hfirst q hq).1⟩) hnp
  intro q hq r hr x hxq hxr
  exact equal_depth_nonperiodic_leaves_disjoint (hodd q hq) (hodd r hr)
    (hfirst q hq) (hfirst r hr) (hdepth q hq) (hdepth r hr)
    (hnp q hq) (hnp r hr) hxq hxr

#print axioms equal_depth_nonperiodic_leaves_disjoint
#print axioms firstHit_cut_coefficient_bound
#print axioms finite_unit_nonperiodic_firstHit_coefficient_bound
end
end CollatzCanonical.PeriodicCensusFloor
